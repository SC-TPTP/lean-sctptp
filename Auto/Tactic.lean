import Lean
import Mathlib
import Auto.Translation
import Auto.Solver.SMT
import Auto.Solver.TPTP
import Auto.Solver.Native
import Auto.LemDB
open Lean Elab Tactic

initialize
  registerTraceClass `auto.tactic
  registerTraceClass `auto.tactic.printProof
  registerTraceClass `auto.printLemmas
  registerTraceClass `auto.runAuto.printLemmas

namespace Auto

/-- `*` : LCtxHyps, `* <ident>` : Lemma database -/
syntax hintelem := term <|> "*" (ident)?
syntax hints := ("[" hintelem,* "]")?
/-- Specify constants to unfold. `unfolds` Must not contain cyclic dependency -/
syntax unfolds := "u[" ident,* "]"
/-- Specify constants to collect definitional equality for -/
syntax defeqs := "d[" ident,* "]"
syntax uord := atomic(unfolds) <|> defeqs
syntax autoinstr := ("👍" <|> "👎")?
syntax (name := auto) "auto" autoinstr hints (uord)* : tactic
syntax (name := egg) "egg" autoinstr hints (uord)* : tactic
syntax (name := mononative) "mononative" hints (uord)* : tactic
syntax (name := intromono) "intromono" hints (uord)* : tactic

inductive Instruction where
  | none
  | useSorry

def parseInstr : TSyntax ``autoinstr → TacticM Instruction
| `(autoinstr|) => return .none
| `(autoinstr|👍) => throwError "Your flattery is appreciated 😎"
| `(autoinstr|👎) => do
  logInfo "I'm terribly sorry. A 'sorry' is sent to you as compensation."
  return .useSorry
| _ => throwUnsupportedSyntax

inductive HintElem where
  -- A user-provided term
  | term     : Term → HintElem
  -- Hint database, not yet supported
  | lemdb    : Name → HintElem
  -- `*` adds all hypotheses in the local context
  -- Also, if `[..]` is not supplied to `auto`, all
  --   hypotheses in the local context are
  --   automatically collected.
  | lctxhyps : HintElem
deriving Inhabited, BEq

def parseHintElem : TSyntax ``hintelem → TacticM HintElem
| `(hintelem| *) => return .lctxhyps
| `(hintelem| * $id:ident) => return .lemdb id.getId
| `(hintelem| $t:term) => return .term t
| _ => throwUnsupportedSyntax

structure InputHints where
  terms    : Array Term := #[]
  lemdbs   : Array Name := #[]
  lctxhyps : Bool       := false
deriving Inhabited, BEq

/-- Parse `hints` to an array of `Term`, which is still syntax -/
def parseHints : TSyntax ``hints → TacticM InputHints
| `(hints| [ $[$hs],* ]) => do
  let mut terms := #[]
  let mut lemdbs := #[]
  let mut lctxhyps := false
  let elems ← hs.mapM parseHintElem
  for elem in elems do
    match elem with
    | .term t => terms := terms.push t
    | .lemdb db => lemdbs := lemdbs.push db
    | .lctxhyps => lctxhyps := true
  return ⟨terms, lemdbs, lctxhyps⟩
| `(hints| ) => return ⟨#[], #[], true⟩
| _ => throwUnsupportedSyntax

private def defeqUnfoldErrHint :=
  "Note that auto does not accept defeq/unfold hints which" ++
  "are let-declarations in the local context, because " ++
  "let-declarations are automatically unfolded by auto."

def parseUnfolds : TSyntax ``unfolds → TacticM (Array Prep.ConstUnfoldInfo)
| `(unfolds| u[ $[$hs],* ]) => do
  let exprs ← hs.mapM (fun i => do
    let some expr ← Term.resolveId? i
      | throwError "{decl_name%} :: Unknown identifier {i}. {defeqUnfoldErrHint}"
    return expr)
  exprs.mapM (fun expr => do
    let some name := expr.constName?
      | throwError "{decl_name%} :: Unknown declaration {expr}. {defeqUnfoldErrHint}"
    Prep.getConstUnfoldInfo name)
| _ => throwUnsupportedSyntax

def parseDefeqs : TSyntax ``defeqs → TacticM (Array Name)
| `(defeqs| d[ $[$hs],* ]) => do
  let exprs ← hs.mapM (fun i => do
    let some expr ← Term.resolveId? i
      | throwError "{decl_name%} :: Unknown identifier {i}. {defeqUnfoldErrHint}"
    return expr)
  exprs.mapM (fun expr => do
    let some name := expr.constName?
      | throwError "{decl_name%} :: Unknown declaration {expr}. {defeqUnfoldErrHint}"
    return name)
| _ => throwUnsupportedSyntax

def parseUOrD : TSyntax ``uord → TacticM (Array Prep.ConstUnfoldInfo ⊕ Array Name)
| `(uord| $unfolds:unfolds) => Sum.inl <$> parseUnfolds unfolds
| `(uord| $defeqs:defeqs) => Sum.inr <$> parseDefeqs defeqs
| _ => throwUnsupportedSyntax

def parseUOrDs (stxs : Array (TSyntax ``uord)) : TacticM (Array Prep.ConstUnfoldInfo × Array Name) := do
  let mut hasUnfolds := false
  let mut hasDefeqs := false
  let mut unfolds := #[]
  let mut defeqs := #[]
  for stx in stxs do
    match ← parseUOrD stx with
    | .inl u =>
      if hasUnfolds then
        throwError "{decl_name%} :: Duplicated unfold hint"
      hasUnfolds := true
      unfolds := u
    | .inr d =>
      if hasDefeqs then
        throwError "{decl_name%} :: Duplicated defeq hint"
      hasDefeqs := true
      defeqs := defeqs.append d
  return (unfolds, defeqs)

def collectLctxLemmas (lctxhyps : Bool) (ngoalAndBinders : Array FVarId) : MetaM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let fVarIds ← if lctxhyps then pure (← getLCtx).getFVarIds else pure ngoalAndBinders
    let mut lemmas := #[]
    for fVarId in fVarIds do
      let decl ← FVarId.getDecl fVarId
      let type ← instantiateMVars decl.type
      if ← Prep.isNonemptyInhabited type then
        continue
      if ¬ decl.isAuxDecl ∧ (← Meta.isProp type) then
        let name ← fVarId.getUserName
        lemmas := lemmas.push ⟨⟨mkFVar fVarId, type, .leaf s!"lctxLem {name}"⟩, #[]⟩
    return lemmas

def collectUserLemmas (terms : Array Term) : TacticM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let mut lemmas := #[]
    for term in terms do
      let ⟨⟨proof, type, deriv⟩, params⟩ ← Prep.elabLemma term (.leaf s!"❰{term}❱")
      if ← Prep.isNonemptyInhabited type then
        throwError "invalid lemma {type}, lemmas should not be inhabitation facts"
      else if ← Meta.isProp type then
        lemmas := lemmas.push ⟨⟨proof, ← instantiateMVars type, deriv⟩, params⟩
      else
        -- **TODO**: Relax condition?
        throwError "invalid lemma {type} for auto, proposition expected"
    return lemmas

def collectHintDBLemmas (names : Array Name) : TacticM (Array Lemma) := do
  let mut hs : Std.HashSet Name := Std.HashSet.empty
  let mut ret : Array Lemma := #[]
  for name in names do
    let .some db ← findLemDB name
      | throwError "unknown lemma database {name}"
    let lemNames ← db.toHashSet
    for lname in lemNames do
      if !hs.contains lname then
        hs := hs.insert lname
        ret := ret.push (← Lemma.ofConst lname (.leaf s!"lemdb {name} {lname}"))
  return ret

def collectDefeqLemmas (names : Array Name) : TacticM (Array Lemma) :=
  Meta.withNewMCtxDepth do
    let lemmas ← names.flatMapM Prep.elabDefEq
    lemmas.mapM (fun (⟨⟨proof, type, deriv⟩, params⟩ : Lemma) => do
      let type ← instantiateMVars type
      return ⟨⟨proof, type, deriv⟩, params⟩)

def unfoldConstAndPreprocessLemma (unfolds : Array Prep.ConstUnfoldInfo) (lem : Lemma) : MetaM Lemma := do
  let type ← prepReduceExpr (← instantiateMVars lem.type)
  let type := Prep.unfoldConsts unfolds type
  let type ← Core.betaReduce (← instantiateMVars type)
  let lem := {lem with type := type}
  return lem

/--
  We assume that all defeq facts have the form
    `∀ (x₁ : ⋯) ⋯ (xₙ : ⋯), c ... = ...`
  where `c` is a constant. To avoid `whnf` from reducing
  `c`, we call `forallTelescope`, then call `prepReduceExpr`
  on
  · All the arguments of `c`, and
  · The right-hand side of the equation
-/
def unfoldConstAndprepReduceDefeq (unfolds : Array Prep.ConstUnfoldInfo) (lem : Lemma) : MetaM Lemma := do
  let .some type ← prepReduceDefeq (← instantiateMVars lem.type)
    | throwError "unfoldConstAndprepReduceDefeq :: Unrecognized definitional equation {lem.type}"
  let type := Prep.unfoldConsts unfolds type
  let type ← Core.betaReduce (← instantiateMVars type)
  let lem := {lem with type := type}
  return lem

def traceLemmas (traceClass : Name) (pre : String) (lemmas : Array Lemma) : CoreM Unit := do
  let mut cnt : Nat := 0
  let mut mdatas : Array MessageData := #[]
  for lem in lemmas do
    mdatas := mdatas.push m!"\n{cnt}: {lem}"
    cnt := cnt + 1
  if ← isTracingEnabledFor traceClass then
    addTrace traceClass (mdatas.foldl MessageData.compose pre)

def checkDuplicatedFact (terms : Array Term) : TacticM Unit :=
  let n := terms.size
  for i in [0:n] do
    for j in [i+1:n] do
      if terms[i]? == terms[j]? then
        throwError "Auto does not accept duplicated input terms"

def checkDuplicatedLemmaDB (names : Array Name) : TacticM Unit :=
  let n := names.size
  for i in [0:n] do
    for j in [i+1:n] do
      if names[i]? == names[j]? then
        throwError "Auto does not accept duplicated lemma databases"

def collectAllLemmas
  (hintstx : TSyntax ``hints) (uords : Array (TSyntax `Auto.uord)) (ngoalAndBinders : Array FVarId) :
  -- The first `Array Lemma` are `Prop` lemmas
  -- The second `Array Lemma` are Inhabitation facts
  TacticM (Array Lemma × Array Lemma) := do
  let inputHints ← parseHints hintstx
  let (unfoldInfos, defeqNames) ← parseUOrDs uords
  let unfoldInfos ← Prep.topoSortUnfolds unfoldInfos
  let startTime ← IO.monoMsNow
  let lctxLemmas ← collectLctxLemmas inputHints.lctxhyps ngoalAndBinders
  let lctxLemmas ← lctxLemmas.mapM (m:=MetaM) (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas `auto.printLemmas "Lemmas collected from local context:" lctxLemmas
  checkDuplicatedFact inputHints.terms
  checkDuplicatedLemmaDB inputHints.lemdbs
  let userLemmas := (← collectUserLemmas inputHints.terms) ++ (← collectHintDBLemmas inputHints.lemdbs)
  let userLemmas ← userLemmas.mapM (m:=MetaM) (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas `auto.printLemmas "Lemmas collected from user-provided terms:" userLemmas
  let defeqLemmas ← collectDefeqLemmas defeqNames
  let defeqLemmas ← defeqLemmas.mapM (m:=MetaM) (unfoldConstAndprepReduceDefeq unfoldInfos)
  traceLemmas `auto.printLemmas "Lemmas collected from user-provided defeq hints:" defeqLemmas
  trace[auto.tactic] "Preprocessing took {(← IO.monoMsNow) - startTime}ms"
  let inhFacts ← Inhabitation.getInhFactsFromLCtx
  let inhFacts ← inhFacts.mapM (m:=MetaM) (unfoldConstAndPreprocessLemma unfoldInfos)
  traceLemmas `auto.printLemmas "Inhabitation lemmas :" inhFacts
  return (lctxLemmas ++ userLemmas ++ defeqLemmas, inhFacts)

open Embedding.Lam in
def queryTPTP (exportFacts : Array REntry) : LamReif.ReifM (Option Expr × Option (Array REntry)) := do
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let exportLamTerms ← exportFacts.mapM (fun re => do
    match re with
    | .valid [] t => return t
    | _ => throwError "{decl_name%} :: Unexpected error")
  let query ← if (auto.mono.mode.get (← getOptions)) == MonoMode.fol then
    lam2FOF lamVarTy lamEVarTy exportLamTerms
  else
    lam2TH0 lamVarTy lamEVarTy exportLamTerms
  trace[auto.tptp.printQuery] "\n{query}"
  let (proven, tptpProof) ← Solver.TPTP.querySolver query
  if !proven then
    return (.none, .none)
  try
    let proofSteps ← Parser.TPTP.getProof lamVarTy lamEVarTy tptpProof
    for step in proofSteps do
      trace[auto.tptp.printProof] "{step}"
  catch e =>
    trace[auto.tptp.printProof] "TPTP proof reification failed with {e.toMessageData}"
  let unsatCoreIds ← Parser.TPTP.unsatCore tptpProof
  let mut unsatCore := #[]
  for n in unsatCoreIds do
    let .some re := exportFacts[n]?
      | throwError "{decl_name%} :: Index {n} out of range"
    unsatCore := unsatCore.push re
  if (auto.tptp.trust.get (← getOptions)) then
    logWarning "Trusting TPTP solvers. `autoTPTPSorry` is used to discharge the goal."
    return (← Meta.mkAppM ``autoTPTPSorry #[Expr.const ``False []], unsatCore)
  else
    return (.none, unsatCore)

open Embedding.Lam in
def querySMT (exportFacts : Array REntry) (exportInds : Array MutualIndInfo) : LamReif.ReifM (Option Expr × Option (Array REntry)) := do
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let exportLamTerms ← exportFacts.mapM (fun re => do
    match re with
    | .valid [] t => return t
    | _ => throwError "{decl_name%} :: Unexpected error")
  let sni : SMT.SMTNamingInfo :=
    {tyVal := (← LamReif.getTyVal), varVal := (← LamReif.getVarVal), lamEVarTy := (← LamReif.getLamEVarTy)}
  let ((commands, validFacts), state) ← (lamFOL2SMT sni lamVarTy lamEVarTy exportLamTerms exportInds).run
  for cmd in commands do
    trace[auto.smt.printCommands] "{cmd}"
  if (auto.smt.save.get (← getOptions)) then
    Solver.SMT.saveQuery commands
  let .some (unsatCore, proof) ← Solver.SMT.querySolver commands
    | return (.none, .none)
  let unsatCoreIds ← Solver.SMT.validFactOfUnsatCore unsatCore
  -- **Print valuation of SMT atoms**
  SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
    for (atomic, name) in state.h2lMap.toArray do
      let e ← SMT.LamAtomic.toLeanExpr tyValMap varValMap etomValMap atomic
      trace[auto.smt.printValuation] "|{name}| : {e}"
    )
  -- **Print STerms corresponding to `validFacts` in unsatCore**
  for id in unsatCoreIds do
    let .some sterm := validFacts[id]?
      | throwError "{decl_name%} :: Index {id} of `validFacts` out of range"
    trace[auto.smt.unsatCore.smtTerms] "|valid_fact_{id}| : {sterm}"
  -- **Print Lean expressions correesponding to `validFacts` in unsatCore**
  SMT.withExprValuation sni state.h2lMap (fun tyValMap varValMap etomValMap => do
    for id in unsatCoreIds do
      let .some t := exportLamTerms[id]?
        | throwError "{decl_name%} :: Index {id} of `exportLamTerms` out of range"
      let e ← Lam2D.interpLamTermAsUnlifted tyValMap varValMap etomValMap 0 t
      trace[auto.smt.unsatCore.leanExprs] "|valid_fact_{id}| : {← Core.betaReduce e}"
    )
  -- **Print derivation of unsatCore**
  for id in unsatCoreIds do
    let .some t := exportLamTerms[id]?
      | throwError "{decl_name%} :: Index {id} of `exportLamTerm` out of range"
    let vderiv ← LamReif.collectDerivFor (.valid [] t)
    trace[auto.smt.unsatCore.deriv] "|valid_fact_{id}| : {vderiv}"
  -- **Getting unsatCore**
  let mut unsatCore := #[]
  for id in unsatCoreIds do
    let .some re := exportFacts[id]?
      | throwError "{decl_name%} :: Index {id}  of `exportFacts` out of range"
    unsatCore := unsatCore.push re
  if auto.smt.rconsProof.get (← getOptions) then
    let (_, _) ← Solver.SMT.getSexp proof
    logWarning "Proof reconstruction is not implemented."
  if (auto.smt.trust.get (← getOptions)) then
    logWarning "Trusting SMT solvers. `autoSMTSorry` is used to discharge the goal."
    return (← Meta.mkAppM ``autoSMTSorry #[Expr.const ``False []], unsatCore)
  else
    return (.none, unsatCore)

open LamReif Embedding.Lam in
/--
  Given
  · `nonempties = #[s₀, s₁, ⋯, sᵤ₋₁]`
  · `valids = #[t₀, t₁, ⋯, kₖ₋₁]`
  Invoke prover to get a proof of
    `proof : (∀ (_ : v₀) (_ : v₁) ⋯ (_ : vᵤ₋₁), w₀ → w₁ → ⋯ → wₗ₋₁ → ⊥).interp`
  and returns
  · `fun etoms => proof`
  · `∀ etoms, ∀ (_ : v₀) (_ : v₁) ⋯ (_ : vᵤ₋₁), w₀ → w₁ → ⋯ → wₗ₋₁ → ⊥)`
  · `etoms`
  · `[s₀, s₁, ⋯, sᵤ₋₁]`
  · `[w₀, w₁, ⋯, wₗ₋₁]`
  Here
  · `[v₀, v₁, ⋯, vᵤ₋₁]` is a subsequence of `[s₀, s₁, ⋯, sᵤ₋₁]`
  · `[w₀, w₁, ⋯, wₗ₋₁]` is a subsequence of `[t₀, t₁, ⋯, kₖ₋₁]`
  · `etoms` are all the etoms present in `w₀ → w₁ → ⋯ → wₗ₋₁ → ⊥`

  Note that `MetaState.withTemporaryLCtx` is used to isolate the prover from the
  current local context. This is necessary because `lean-auto` assumes that the prover
  does not use free variables introduced during monomorphization
-/
def callNative_checker
  (nonempties : Array REntry) (valids : Array REntry) (prover : Array Lemma → Array Lemma → MetaM Expr) :
  ReifM (Expr × LamTerm × Array Nat × Array REntry × Array REntry) := do
  let tyVal ← LamReif.getTyVal
  let varVal ← LamReif.getVarVal
  let lamEVarTy ← LamReif.getLamEVarTy
  let nonemptiesWithDTr ← nonempties.mapM (fun re =>
    do return (re, ← collectDerivFor re))
  let validsWithDTr ← valids.mapM (fun re =>
    do return (re, ← collectDerivFor re))
  MetaState.runAtMetaM' <| (Lam2DAAF.callNativeWithAtomAsFVar nonemptiesWithDTr validsWithDTr prover).run'
    { tyVal := tyVal, varVal := varVal, lamEVarTy := lamEVarTy }

open LamReif Embedding.Lam in
/--
  Similar in functionality compared to `callNative_checker`, but
  all `valid` entries are supposed to be reified facts (so there should
  be no `etom`s). We invoke the prover to get the same `proof` as
  `callNativeChecker`, but we return a proof of `⊥` by applying `proof`
  to un-reified facts.

  Note that `MetaState.withTemporaryLCtx` is used to isolate the prover from the
  current local context. This is necessary because `lean-auto` assumes that the prover
  does not use free variables introduced during monomorphization
-/
def callNative_direct
  (nonempties : Array REntry) (valids : Array REntry) (prover : Array Lemma → Array Lemma → MetaM Expr) : ReifM Expr := do
  let tyVal ← LamReif.getTyVal
  let varVal ← LamReif.getVarVal
  let lamEVarTy ← LamReif.getLamEVarTy
  let nonemptiesWithDTr ← nonempties.mapM (fun re =>
    do return (re, ← collectDerivFor re))
  let validsWithDTr ← valids.mapM (fun re =>
    do return (re, ← collectDerivFor re))
  let (proof, _, usedEtoms, usedInhs, usedHyps) ← MetaState.runAtMetaM' <|
    (Lam2DAAF.callNativeWithAtomAsFVar nonemptiesWithDTr validsWithDTr prover).run'
      { tyVal := tyVal, varVal := varVal, lamEVarTy := lamEVarTy }
  if usedEtoms.size != 0 then
    throwError "{decl_name%} :: etoms should not occur here"
  let ss ← usedInhs.mapM (fun re => do
    match ← lookupREntryProof! re with
    | .inhabitation e _ _ => return e
    | .chkStep (.n (.nonemptyOfAtom n)) =>
      match varVal[n]? with
      | .some (e, _) => return e
      | .none => throwError "{decl_name%} :: Unexpected error"
    | _ => throwError "{decl_name%} :: Cannot find external proof of {re}")
  let ts ← usedHyps.mapM (fun re => do
    let .assertion e _ _ ← lookupREntryProof! re
      | throwError "{decl_name%} :: Cannot find external proof of {re}"
    return e)
  return mkAppN proof (ss ++ ts)

open Embedding.Lam in
/--
  If `prover?` is specified, use the specified one.
  Otherwise use the one determined by `Solver.Native.queryNative`
-/
def queryNative
  (declName? : Option Name) (exportFacts exportInhs : Array REntry)
  (prover? : Option (Array Lemma → Array Lemma → MetaM Expr) := .none) : LamReif.ReifM (Option Expr) := do
  let (proof, proofLamTerm, usedEtoms, usedInhs, unsatCore) ←
    callNative_checker exportInhs exportFacts (prover?.getD Solver.Native.queryNative)
  LamReif.newAssertion proof (.leaf "by_native::queryNative") proofLamTerm
  let etomInstantiated ← LamReif.validOfInstantiateForall (.valid [] proofLamTerm) (usedEtoms.map .etom)
  let forallElimed ← LamReif.validOfElimForalls etomInstantiated usedInhs
  let contra ← LamReif.validOfImps forallElimed unsatCore
  LamReif.printProofs
  Reif.setDeclName? declName?
  let checker ← LamReif.buildCheckerExprFor contra
  Meta.mkAppM ``Embedding.Lam.LamThmValid.getFalse #[checker]

def rewriteIteCondDecide (lemmas : Array Lemma) : MetaM (Array Lemma) := do
  -- Simplify `ite`
  let ite_simp_lem ← Lemma.ofConst ``Auto.Bool.ite_simp (.leaf "hw Auto.Bool.ite_simp")
  let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem ite_simp_lem)
  -- Simplify `cond`
  let cond_simp_lem ← Lemma.ofConst ``Auto.Bool.cond_simp (.leaf "hw Auto.Bool.cond_simp")
  let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem cond_simp_lem)
  -- Simplify `decide`
  let decide_simp_lem ← Lemma.ofConst ``Auto.Bool.decide_simp (.leaf "hw Auto.Bool.decide_simp")
  let lemmas ← lemmas.mapM (fun lem => Lemma.rewriteUPolyRigid lem decide_simp_lem)
  return lemmas

/--
  Run `auto`'s monomorphization and preprocessing, then send the problem to different solvers
-/
def runAuto
  (declName? : Option Name) (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM Expr :=
  Meta.withDefault do
    traceLemmas `auto.runAuto.printLemmas s!"All lemmas received by {decl_name%}:" lemmas
    let lemmas ← rewriteIteCondDecide lemmas
    let (proof, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (reifMAction s.facts s.inhTys s.inds).run' {u := u})
    trace[auto.tactic] "Auto found proof of {← Meta.inferType proof}"
    trace[auto.tactic.printProof] "{proof}"
    return proof
where
  reifMAction
    (uvalids : Array UMonoFact) (uinhs : Array UMonoFact)
    (minds : Array (Array SimpleIndVal)) : LamReif.ReifM Expr := do
    let exportFacts ← LamReif.reifFacts uvalids
    let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInhs := (← LamReif.getRst).nonemptyMap.toArray.map
      (fun (s, _) => Embedding.Lam.REntry.nonempty s)
    let exportInds ← LamReif.reifMutInds minds
    LamReif.printValuation
    -- **Preprocessing in Verified Checker**
    let (exportFacts', exportInds) ← LamReif.preprocess exportFacts exportInds
    exportFacts := exportFacts'
    -- **TPTP invocation and Premise Selection**
    if auto.tptp.get (← getOptions) then
      let (proof, unsatCore) ← queryTPTP exportFacts
      if let .some proof := proof then
        return proof
      let premiseSel? := auto.tptp.premiseSelection.get (← getOptions)
      if premiseSel? then
        if let .some unsatCore := unsatCore then
          exportFacts := unsatCore
    -- **SMT**
    if auto.smt.get (← getOptions) then
      let (proof, _) ← querySMT exportFacts exportInds
      if let .some proof := proof then
        return proof
    -- **Native Prover**
    exportFacts := exportFacts.append (← LamReif.auxLemmas exportFacts)
    if auto.native.get (← getOptions) then
      if let .some proof ← queryNative declName? exportFacts exportInhs then
        return proof
    throwError "Auto failed to find proof"

@[tactic auto]
def evalAuto : Tactic
| `(auto | auto $instr $hints $[$uords]*) => withMainContext do
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "{decl_name%} :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let instr ← parseInstr instr
    match instr with
    | .none =>
      let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push ngoal)
      let declName? ← Elab.Term.getDeclName?
      let proof ← runAuto declName? lemmas inhFacts
      absurd.assign proof
    | .useSorry =>
      let proof ← Meta.mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
      absurd.assign proof
| _ => throwUnsupportedSyntax

@[tactic intromono]
def evalIntromono : Tactic
| `(intromono | intromono $hints $[$uords]*) => withMainContext do
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "{decl_name%} :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, _) ← collectAllLemmas hints uords (goalBinders.push ngoal)
    let newMid ← Monomorphization.intromono lemmas absurd
    replaceMainGoal [newMid]
| _ => throwUnsupportedSyntax

/--
  A monomorphization interface that can be invoked by repos dependent on `lean-auto`.
-/
def monoInterface
  (lemmas : Array Lemma) (inhFacts : Array Lemma)
  (prover : Array Lemma → Array Lemma → MetaM Expr) : MetaM Expr := do
  let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) : LamReif.ReifM Expr := (do
    let exportFacts ← LamReif.reifFacts uvalids
    let exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInhs := (← LamReif.getRst).nonemptyMap.toArray.map
      (fun (s, _) => Embedding.Lam.REntry.nonempty s)
    LamReif.printValuation
    callNative_direct exportInhs exportFacts prover)
  let (proof, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
    let uvalids ← liftM <| Reif.getFacts
    let uinhs ← liftM <| Reif.getInhTys
    let u ← computeMaxLevel uvalids
    (afterReify uvalids uinhs).run' {u := u})
  return proof

/--
  Run native `prover` with monomorphization and preprocessing of `auto`
-/
def runNativeProverWithAuto
  (declName? : Option Name) (prover : Array Lemma → Array Lemma → MetaM Expr)
  (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM Expr := do
  let afterReify (uvalids : Array UMonoFact) (uinhs : Array UMonoFact) : LamReif.ReifM Expr := (do
    let exportFacts ← LamReif.reifFacts uvalids
    let exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    let exportInhs := (← LamReif.getRst).nonemptyMap.toArray.map
      (fun (s, _) => Embedding.Lam.REntry.nonempty s)
    LamReif.printValuation
    let (exportFacts, _) ← LamReif.preprocess exportFacts #[]
    if let .some expr ← queryNative declName? exportFacts exportInhs prover then
      return expr
    else
      throwError "{decl_name%} :: Failed to find proof")
  let (proof, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM Expr) do
    let s ← get
    let u ← computeMaxLevel s.facts
    (afterReify s.facts s.inhTys).run' {u := u})
  trace[auto.tactic] "{decl_name%} :: Found proof of {← Meta.inferType proof}"
  return proof

@[tactic mononative]
def evalMonoNative : Tactic
| `(mononative | mononative $hints $[$uords]*) => withMainContext do
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let [nngoal] ← newGoal.apply (.const ``Classical.byContradiction [])
    | throwError "{decl_name%} :: Unexpected result after applying Classical.byContradiction"
  let (ngoal, absurd) ← MVarId.intro1 nngoal
  replaceMainGoal [absurd]
  withMainContext do
    let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push ngoal)
    let proof ← monoInterface lemmas inhFacts Solver.Native.queryNative
    absurd.assign proof
| _ => throwUnsupportedSyntax



/- #####################################
  SC-TPTP related code
##################################### -/


open Embedding.Lam in
def queryTPTPEgg (exportFacts : Array REntry) : LamReif.ReifM (Array Parser.TPTP.ProofStep) := do
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let exportLamTerms ← exportFacts.mapM (fun re => do
    match re with
    | .valid [] t => return t
    | _ => throwError "{decl_name%} :: Unexpected error")
  let query ← if (auto.mono.mode.get (← getOptions)) == MonoMode.fol then
    lam2FOF lamVarTy lamEVarTy exportLamTerms
  else
    lam2TH0 lamVarTy lamEVarTy exportLamTerms
  trace[auto.tptp.printQuery] "\n{query}"
  let (proven, tptpProof) ← Solver.TPTP.querySolver query
  if proven then
    try
      let proofSteps ← Parser.TPTP.getSCTPTPProof tptpProof
      return proofSteps
    catch e =>
      throwError "Egg found a proof, but proof reification failed with {e.toMessageData}"
  else
    throwError "Egg failed to find proof"


open Lean Elab Tactic Meta

/--
A helper that, given a name and an expression for the type (P), creates
a new goal for proving P and adds a hypothesis (H : P) to the current goal.
-/
def haveExpr (hName : Name) (p : Expr) : TacticM Unit := do
  -- current goal is G.
  let currentMainGoal ← getMainGoal

  -- Create a new goal to prove p.
  let newGoal ← mkFreshExprMVar (.some p) (userName := hName)

  -- Assert is essentially the Expr level of `have`.
  let newMainGoal ← currentMainGoal.assert hName p newGoal
  -- We then need to introduce the binding into the context.
  let (_fvar, newMainGoal) ← newMainGoal.intro1P

  -- set the goal to the `have` goal and the new main goal with the have introduced.
  replaceMainGoal [newGoal.mvarId!, newMainGoal]

-- Test the implementation of `haveExpr`
example : True := by
  run_tac do
    haveExpr `Random (← elabTerm (← `(True)) .none)
  · exact True.intro
  · exact Random

#check LocalContext
def evalSpecialize (n : Name) (e : Expr) : TacticM Unit := withMainContext do
  -- let (e, mvarIds') ← elabTermWithHoles e none `specialize (allowNaturalHoles := true)
  let lctx ← getLCtx
  let .some localDecl := lctx.findFromUserName? n
    | throwError m!"{decl_name%} : Could not find {n} in context"
  let applied := .app (.fvar localDecl.fvarId) e
  let mvarId ← (← getMainGoal).assert localDecl.userName (← inferType applied).headBeta applied
  let (_, mvarId) ← mvarId.intro1P
  let mvarId ← mvarId.tryClear localDecl.fvarId
  replaceMainGoal [mvarId]

example : True := by
  run_tac do
    haveExpr `Random (← elabTerm (← `(True → True)) .none)
  · exact fun _ => True.intro
  · run_tac evalSpecialize `Random (← elabTerm (← `(True.intro)) .none)
    exact Random

def getHypExpr (n : Name) : TacticM Expr := withMainContext do
  let lctx ← getLCtx
  let .some localDecl := lctx.findFromUserName? n
    | throwError m!"{decl_name%} : Could not find {n} in context {lctx.getFVars}"
  return ← instantiateMVars localDecl.type

def getHypName (e : Expr) (addNot : Bool := False) : TacticM Name := withMainContext do
  let mut e := e
  if addNot then
    e := mkApp (mkConst ``Not) e
  let lctx ← getLCtx
  for decl in lctx do
    let ty := decl.type
    if ← isDefEq ty e then
      return decl.userName

  -- build error message by appending all hypotheses
  e ← Core.betaReduce (← instantiateMVars e)
  let mut s := ""
  for decl in lctx do
    let ty ← Core.betaReduce (← instantiateMVars decl.type)
    s := s ++ s!"- {decl.userName} : {ty}\n"
  let goalStr ← (← getMainGoal).getType
  throwError s!"Cannot find hypothesis for `{e}` in context:\n{s}\n|- {goalStr}"

open Parser.TPTP Parser.TPTP.InferenceRule in
/-- Given a parsed and reified TPTP proofstep, dispatch to the corresponding Lean tactic(s). -/
def applyProofStep (proofstep : ProofStep) (premisesProofstep : Array ProofStep) : TacticM Unit := withMainContext do
  let psName := (.str .anonymous proofstep.name)

  match proofstep.rule with
  -- Level 1
  | leftFalse _ => do evalTactic (← `(tactic| assumption))
  | rightTrue _ => do evalTactic (← `(tactic| assumption))
  | hyp _       => do evalTactic (← `(tactic| contradiction))
  | leftWeaken _ => pure ()
  | rightWeaken _ => pure ()

  | cut i => do
    let formula := premisesProofstep[0]!.consequents[i]!
    haveExpr psName formula
    evalTactic (← `(tactic| apply Classical.byContradiction; intro $(mkIdent psName):ident))

  | leftAnd i => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let (hypName1, hypName2) := (Name.str hypName "1", Name.str hypName "2")
    evalTactic (← `(tactic| cases $(mkIdent hypName):ident; rename_i $(mkIdent hypName1):ident $(mkIdent hypName2):ident))

  | leftOr i => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| cases $(mkIdent hypName):ident <;> rename_i $(mkIdent newHypName):ident))

  | leftImplies i => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| rw [imp_iff_not_or] at $(mkIdent hypName):ident))
    evalTactic (← `(tactic| cases $(mkIdent hypName):ident <;> rename_i $(mkIdent newHypName):ident))

  | leftIff i => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let (hypName1, hypName2) := (Name.str hypName "1", Name.str hypName "2")
    evalTactic (← `(tactic| cases $(mkIdent hypName):ident; rename_i $(mkIdent hypName1):ident $(mkIdent hypName2):ident))

  | leftNot _ => pure ()

  | leftEx i y => do
    let hypName ← getHypName proofstep.consequents[i]! true
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| rcases $(mkIdent hypName):ident with ⟨$(mkIdent (.str .anonymous y)), $(mkIdent newHypName)⟩))

  | leftForall i t => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| have $(mkIdent newHypName) := $(mkIdent hypName)))
    match t with
    | none => evalTactic (← `(tactic| specialize $(mkIdent newHypName):ident ‹_›))
    | some t => evalSpecialize newHypName t

  | rightAnd i => do
    let hypName ← getHypName proofstep.antecedents[i]! true
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| cases (Classical.not_and_iff_or_not_not.mp $(mkIdent hypName)) <;> rename_i $(mkIdent newHypName):ident))

  | rightOr i => do
    let hypName ← getHypName proofstep.antecedents[i]! true
    let (hypName1, hypName2) := (Name.str hypName "1", Name.str hypName "2")
    evalTactic (← `(tactic| rcases (not_or.mp $(mkIdent hypName)) with ⟨$(mkIdent hypName1), $(mkIdent hypName2)⟩))

  | rightImplies i => do
    let hypName ← getHypName proofstep.consequents[i]! true
    let (hypName1, hypName2) := (Name.str hypName "1", Name.str hypName "2")
    evalTactic (← `(tactic| rcases (Classical.not_imp.mp $(mkIdent hypName)) with ⟨$(mkIdent hypName1):ident, $(mkIdent hypName2)⟩))

  | rightIff i => do
    let hypName ← getHypName proofstep.consequents[i]! true
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| have $(mkIdent newHypName):ident := $(mkIdent hypName):ident))
    evalTactic (← `(tactic| rw [iff_iff_implies_and_implies] at $(mkIdent newHypName):ident))
    evalTactic (← `(tactic| cases (Classical.not_and_iff_or_not_not.mp $(mkIdent newHypName)) <;> rename_i $(mkIdent newHypName):ident))

  | rightNot i => do
    let hypName ← getHypName proofstep.consequents[i]! true
    evalTactic (← `(tactic| apply $(mkIdent hypName); intro $(mkIdent psName):ident))

  | rightEx i t => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| have $(mkIdent newHypName) := $(mkIdent hypName)))
    evalTactic (← `(tactic| rw [not_exists] at $(mkIdent newHypName):ident))
    match t with
    | none => evalTactic (← `(tactic| specialize $(mkIdent newHypName) ‹_›))
    | some t => evalSpecialize newHypName t

  | rightForall i y => do
    let hypName ← getHypName proofstep.consequents[i]! true
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| rcases (Classical.not_forall.mp $(mkIdent hypName)) with ⟨$(mkIdent (.str .anonymous y)), $(mkIdent newHypName)⟩))

  | rightRefl _ => do evalTactic (← `(tactic| contradiction))

  | rightSubstEq i backward P => do
    let equality := proofstep.antecedents[i]!
    let (t, u) ← match equality with
      | Expr.app (.app (.app (.const ``Eq _) _) t) u =>
        if backward then
          pure (u, t)
        else
          pure (t, u)
      | _ => throwError s!"rightSubstEq: cannot find equality in the antecedent form {equality}"
    let eqHypName ← getHypName equality
    let P_u_hypName ← getHypName (P.app u) true
    let newHypName := Name.str P_u_hypName "0"
    -- TODO: use (motive := P)
    evalTactic (← `(tactic| apply $(mkIdent P_u_hypName); first | apply Eq.subst $(mkIdent eqHypName) | apply Eq.subst $(mkIdent eqHypName).symm | rw [$(mkIdent eqHypName):term] | rw [←$(mkIdent eqHypName):term]))
    evalTactic (← `(tactic| apply Classical.byContradiction; intro $(mkIdent newHypName):ident))

  | leftSubstEq i backward P => do
    let equality := proofstep.antecedents[i]!
    let (t, u) ← match equality with
      | Expr.app (.app (.app (.const ``Eq _) _) t) u =>
        if backward then
          pure (u, t)
        else
          pure (t, u)
      | _ => throwError s!"leftSubstEq: cannot find equality in the antecedent form {equality}"
    let eqHypName ← getHypName equality
    let P_u_hypName ← getHypName (P.app u)
    let newHypName := Name.str P_u_hypName "0"
    -- TODO: use (motive := P)
    -- TODO: apply does not work here because it is not negated
    evalTactic (← `(tactic| apply $(mkIdent P_u_hypName); first | apply Eq.subst $(mkIdent eqHypName) | apply Eq.subst $(mkIdent eqHypName).symm | rw [$(mkIdent eqHypName):term] | rw [←$(mkIdent eqHypName):term]))
    evalTactic (← `(tactic| apply Classical.byContradiction; intro $(mkIdent newHypName):ident))

  | rightSubstIff i backward R => do
    let equivalence := proofstep.antecedents[i]!
    let (phi, psi) ← match equivalence with
      | Expr.app (.app (.const ``Iff _) phi) psi =>
        if backward then
          pure (psi, phi)
        else
          pure (phi, psi)
      | _ => throwError s!"rightSubstIff: cannot find equivalence in the antecedent form {equivalence}"
    let eqHypName ← getHypName equivalence
    let R_psi_hypName ← getHypName (R.app psi) true
    let newHypName := Name.str R_psi_hypName "0"
    -- TODO: use (p := P)
    evalTactic (← `(tactic| apply $(mkIdent R_psi_hypName); first | apply Iff.subst $(mkIdent eqHypName) | apply Iff.subst $(mkIdent eqHypName).symm | rw [$(mkIdent eqHypName):term] | rw [←$(mkIdent eqHypName):term]))
    evalTactic (← `(tactic| apply Classical.byContradiction; intro $(mkIdent newHypName):ident))

  | leftSubstIff i backward R => do
    let equivalence := proofstep.antecedents[i]!
    let (phi, psi) ← match equivalence with
      | Expr.app (.app (.const ``Iff _) phi) psi =>
        if backward then
          pure (psi, phi)
        else
          pure (phi, psi)
      | _ => throwError s!"leftSubstIff: cannot find equivalence in the antecedent form {equivalence}"
    let eqHypName ← getHypName equivalence
    let R_psi_hypName ← getHypName (R.app psi)
    let newHypName := Name.str R_psi_hypName "0"
    -- TODO: use (p := P)
    -- TODO: apply does not work here because it is not negated
    evalTactic (← `(tactic| apply $(mkIdent R_psi_hypName); first | apply Iff.subst $(mkIdent eqHypName) | apply Iff.subst $(mkIdent eqHypName).symm | rw [$(mkIdent eqHypName):term] | rw [←$(mkIdent eqHypName):term]))
    evalTactic (← `(tactic| apply Classical.byContradiction; intro $(mkIdent newHypName):ident))

  | instFun funName termStr args => do evalTactic (← `(tactic| sorry))
  | instPred predName formula args => do evalTactic (← `(tactic| sorry))
  | rightEpsilon A X t => do evalTactic (← `(tactic| sorry))
  | leftEpsilon i y => do evalTactic (← `(tactic| sorry))

  -- Level 2
  | congruence => do evalTactic (← `(tactic| repeat trivial))
  | leftHyp _ _ => do evalTactic (← `(tactic| contradiction))

  | leftNotAnd i => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| cases (Classical.not_and_iff_or_not_not.mp $(mkIdent hypName)) <;> rename_i $(mkIdent newHypName):ident))

  | leftNotOr i => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let (hypName1, hypName2) := (Name.str hypName "1", Name.str hypName "2")
    evalTactic (← `(tactic| rcases (not_or.mp $(mkIdent hypName)) with ⟨$(mkIdent hypName1), $(mkIdent hypName2)⟩))

  | leftNotImplies i => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let (hypName1, hypName2) := (Name.str hypName "1", Name.str hypName "2")
    evalTactic (← `(tactic| rcases (not_imp.mp $(mkIdent hypName)) with ⟨$(mkIdent hypName1), $(mkIdent hypName2)⟩))

  | leftNotIff i => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| have $(mkIdent newHypName) := $(mkIdent hypName)))
    evalTactic (← `(tactic| rw [iff_iff_implies_and_implies] at $(mkIdent newHypName):ident))
    evalTactic (← `(tactic| cases (Classical.not_and_iff_or_not_not.mp $(mkIdent newHypName)) <;> rename_i $(mkIdent newHypName):ident))

  | leftNotNot i =>
    let hypName ← getHypName proofstep.antecedents[i]!
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| have $(mkIdent newHypName) := $(mkIdent hypName)))
    evalTactic (← `(tactic| rw [Classical.not_not] at $(mkIdent newHypName):ident))

  | leftNotEx i t => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| have $(mkIdent newHypName) := $(mkIdent hypName)))
    evalTactic (← `(tactic| rw [not_exists] at $(mkIdent newHypName):ident))
    match t with
    | none => evalTactic (← `(tactic| specialize $(mkIdent newHypName) ‹_›))
    | some t => evalSpecialize newHypName t

  | leftNotAll i y => do
    let hypName ← getHypName proofstep.antecedents[i]!
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| rcases (Classical.not_forall.mp $(mkIdent hypName)) with ⟨$(mkIdent (.str .anonymous y)), $(mkIdent newHypName)⟩))

  -- Level 3
  | rightRelIff _ => do evalTactic (← `(tactic| trivial))
  | rightSubstMulti i P vars => do evalTactic (← `(tactic| sorry))
  | leftSubstMulti i P vars => do evalTactic (← `(tactic| sorry))
  | rightSubstEqForallLocal i R Z => do evalTactic (← `(tactic| sorry))
  | rightSubstEqForall i R Z => do evalTactic (← `(tactic| sorry))
  | rightSubstIffForallLocal i R Z => do evalTactic (← `(tactic| sorry))
  | rightSubstIffForall i R Z => do evalTactic (← `(tactic| sorry))

  | rightNnf i j => do
    let hypName ← getHypName proofstep.consequents[i]!
    let targetExpr := mkApp (mkConst ``Not) premisesProofstep[0]!.consequents[j]!
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| have $(mkIdent newHypName) := $(mkIdent hypName)))
    haveExpr psName targetExpr
    evalTactic (← `(tactic| push_neg; push_neg at $(mkIdent psName):ident; exact $(mkIdent psName):ident))

  | rightPrenex i j => do
    let hypName ← getHypName proofstep.consequents[i]!
    let targetExpr := mkApp (mkConst ``Not) premisesProofstep[0]!.consequents[j]!
    let newHypName := Name.str hypName "0"
    evalTactic (← `(tactic| have $(mkIdent newHypName) := $(mkIdent hypName)))
    haveExpr psName targetExpr
    try
      -- TODO: add missing simp rules/theorems
      evalTactic (← `(tactic| push_neg; solve | simpa | simpa [*] | simp_all))
    catch e =>
      throwError s!"Prenex normalization failed, you are probably missing a `Nonempty` instance. Error message:\n{← e.toMessageData.toString}"

  | clausify _ => do evalTactic (← `(tactic| tauto))
  | elimIffRefl i j => do evalTactic (← `(tactic| sorry))
  | instMult triplets => do evalTactic (← `(tactic| sorry))


partial def reconstructProof (proofsteps : Array Parser.TPTP.ProofStep)
  (proofStepNameToIndex : Std.HashMap String Nat)
: TacticM Unit := do
  if proofsteps.size != 0 then
    let proofstep := proofsteps[proofsteps.size - 1]!
    trace[auto.tptp.printProof] s!"  {proofstep}"
    let premises := proofstep.premises.map (fun i => proofStepNameToIndex.get! i)
    let premisesProofstep := premises.map (fun i => proofsteps[i]!)
    trace[auto.tptp.printProof] s!"    Premises: {premisesProofstep.map (fun ps => ps.name)}"
    applyProofStep proofstep premisesProofstep.toArray
    for premise in premises do
      reconstructProof (proofsteps.toSubarray 0 (premise+1)) proofStepNameToIndex

/--
  Run `auto`'s monomorphization and preprocessing, then send the problem to Egg solver
-/
def runEgg
  (lemmas : Array Lemma) (inhFacts : Array Lemma) : MetaM (Array Parser.TPTP.ProofStep) :=
  withDefault do
    traceLemmas `auto.runAuto.printLemmas s!"All lemmas received by {decl_name%}:" lemmas
    let lemmas ← rewriteIteCondDecide lemmas
    let (proofsteps, _) ← Monomorphization.monomorphize lemmas inhFacts (@id (Reif.ReifM (Array Parser.TPTP.ProofStep)) do
      let s ← get
      let u ← computeMaxLevel s.facts
      (reifMAction s.facts s.inhTys s.inds).run' {u := u})
    return proofsteps
where
  reifMAction
    (uvalids : Array UMonoFact) (uinhs : Array UMonoFact)
    (minds : Array (Array SimpleIndVal)) : LamReif.ReifM (Array Parser.TPTP.ProofStep) := do
    let exportFacts ← LamReif.reifFacts uvalids
    let mut exportFacts := exportFacts.map (Embedding.Lam.REntry.valid [])
    let _ ← LamReif.reifInhabitations uinhs
    -- let exportInds ← LamReif.reifMutInds minds
    LamReif.printValuation
    -- -- **Preprocessing in Verified Checker**
    -- let (exportFacts', _) ← LamReif.preprocess exportFacts exportInds
    -- exportFacts := exportFacts'
    -- **TPTP invocation and Premise Selection**
    if auto.tptp.get (← getOptions) then
      let proofsteps ← queryTPTPEgg exportFacts
      return proofsteps
    throwError "auto.tptp is not enabled"

#check LocalContext
@[tactic egg]
def evalEgg : Tactic
| `(egg | egg $instr $hints $[$uords]*) => withMainContext do
  -- Suppose the goal is `∀ (x₁ x₂ ⋯ xₙ), G`
  -- First, apply `intros` to put `x₁ x₂ ⋯ xₙ` into the local context,
  --   now the goal is just `G`
  let (goalBinders, newGoal) ← (← getMainGoal).intros
  let currentGoalName := `_currentGoalName
  liftMetaTactic fun g => do
    let [newG] ← g.apply (.const ``Classical.byContradiction [])
      | throwError "{decl_name%} :: Too many arguments"
    let newG ← newG.introN 1 [currentGoalName]
    return [newG.2]

  let instr ← parseInstr instr
  match instr with
  | .none => withMainContext do
    let (lemmas, inhFacts) ← collectAllLemmas hints uords (goalBinders.push (FVarId.mk `_currentGoalName))
    let proofsteps ← runEgg lemmas inhFacts

    -- -- Trick: add original hypotheses as ProofStep with the `hyp` rule
    -- let lemmas := lemmas.eraseIdx! (lemmas.size -1) -- drop last lemmas as it is the negated goal
    -- let proofsteps := (lemmas.zipWithIndex.map (fun (lmma, i) =>{
    --   name := s!"a{i}",
    --   rule := .hyp i,
    --   antecedents := [],
    --   consequents := [lmma.type],
    --   premises := []
    -- })) ++ proofsteps

    trace[auto.tptp.printProof] "Proof steps (forward):"
    for step in proofsteps do
      trace[auto.tptp.printProof] "  {step}"

    try
      let mut proofStepNameToIndex : Std.HashMap String Nat := Std.HashMap.empty
      for (proofstep, i) in proofsteps.zipWithIndex do
        proofStepNameToIndex := proofStepNameToIndex.insert proofstep.name i
      trace[auto.tptp.printProof] "Proof steps (backward):"
      reconstructProof proofsteps proofStepNameToIndex
    catch e =>
      throwError "Egg found a proof, but reconstruction failed with:\n{e.toMessageData}"
  | .useSorry =>
    let proof ← mkAppM ``sorryAx #[Expr.const ``False [], Expr.const ``false []]
    newGoal.assign proof
| _ => throwUnsupportedSyntax

end Auto


set_option auto.tptp true
set_option auto.tptp.solver.name "egg"
set_option auto.tptp.egg.path "/home/poiroux/Documents/EPFL/PhD/Lean/lean-auto/egg-sc-tptp"
set_option auto.mono.mode "fol"
-- set_option auto.lamReif.prep.def false

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.printProof true
set_option trace.auto.tptp.result true
set_option trace.auto.lamReif.printValuation true


example : A ↔ A := by
  egg

example : A = A := by
  egg

example (α : Type) (a b c d e : α)
  (h : ∀ y : Nat, ∃ x, x = y)
  (h1 : a = b)
  (h2 : b = c)
  (h3 : c = d)
  (h4 : d = e) :
  a = e := by
  egg

example (α : Type) (f : α -> α) (a : α)
  (h1 : a = (fun x => f x) a) :
  a = f a := by
  egg

example (α : Type) (f : α -> α) (a : α)
  (h1 : ∀ x, x = (f (f (f ( f x)))))
  (h2 : a =  f (f (f (f ( f a))))) :
  a = f a := by
  egg

example (α : Type) (f : α -> α) (a : α)
  (h1 : ∀ x, (f (f (f ( f x)))) = x)
  (h2 : a =  f (f (f (f ( f a))))) :
  a = f a := by
  egg

theorem saturation (α : Type) (sf : α -> α) (cemptySet : α)
  (h1 : ∀ x, x = sf (sf (sf x)))
  (h2 : ∀ x, (∀ y : α, x = sf (sf x))) :
  cemptySet = sf cemptySet := by
  egg

theorem testiff (α : Type) (p : α -> Prop) (sf : α -> α) (cemptySet : α)
  (h1 : ∀ x, p x ↔ p (sf (sf (sf (sf (sf (sf (sf (sf x)))))))))
  (h2 : ∀ x, p x ↔ p (sf (sf (sf (sf (sf x)))))) :
  p (sf cemptySet) ↔ p cemptySet := by
  egg

example (α : Type) (sf : α -> α)
  (h1 : ∀ x, x = sf (sf (sf x)))
  (h2 : ∀ x, (∀ y : α, x = sf (sf x))) :
  ∀ x, x = sf x := by
  egg

example (α : Type) (f : α -> α) (a : α)
  (h1 : ∀ x, x = (f (f (f ( f x)))))
  (h2 : a =  f (f (f (f ( f a))))) :
  f a = a := by
  egg
