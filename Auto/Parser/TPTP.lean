import Lean
import Auto.Embedding.LamBVarOp
import Std.Data.HashMap
import Auto.Translation.LamReif
import Auto.Translation.LamUtils

open Lean.Meta
open Lean

namespace Auto.Parser.TPTP

namespace Tokenizer

inductive Status where
  | default
  | ident
  | string
  | comment
  deriving Repr, BEq

inductive Token where
  | op (op : String)
  | ident (ident : String)
  deriving Repr, Inhabited, BEq

def Token.toString : Token → String
| .op a => a
| .ident a => a

instance : ToString Token where
  toString := Token.toString

structure State where
  input     : String
  pos       : Nat := 0
  status    : Status := .default
  currToken : String := ""
  res       : Array Token := #[]
deriving Repr

def tokens := [
  "@", "|", "&", "<=>", "=>", "<=", "<~>", "~|", "~&", ">", "=", "!=", "!!", "??",
  "~", ",", "(", ")", "*", "!", "?", "^", ":", "[", "]", "!>", ".", "*", "-->"
]

def tokenHashMap : Std.HashSet String :=
  Std.HashSet.empty.insertMany tokens

def tokenPrefixes : Std.HashSet String :=
  Std.HashSet.empty.insertMany $ tokens.flatMap (fun t => Id.run do
    let mut res := []
    let mut pref := ""
    for c in t.data do
      pref := pref.push c
      res := pref :: res
    return res
)

abbrev TokenizerM := StateRefT State IO

def setStatus (status : Status) : TokenizerM Unit := do
  modify (fun (s : State) => {s with status := status})

def getStatus : TokenizerM Status := do
  return (← get).status

def addToCurrToken (char : Char) : TokenizerM Unit := do
  modify (fun (s : State) => {s with currToken := s.currToken.push char})

def getCurrToken : TokenizerM String := do
  return (← get).currToken

def addCurrToken : TokenizerM Unit := do
  modify fun (s : State) =>
    {s with
      res := s.res.push $
        match s.status with
        | .default => .op s.currToken
        | .ident => .ident s.currToken
        | .string => .ident s.currToken
        | .comment => panic! s!"Cannot add comment as token"
      currToken := ""
    }

def finalizeToken : TokenizerM Unit := do
  if (← getStatus) == .string || (← getCurrToken) != "" then
    match ← getStatus with
    | .default =>
      if tokenHashMap.contains (← getCurrToken)
      then addCurrToken
      else throw $ IO.userError s!"TPTP.parse.finalizeToken :: Invalid token: {(← getCurrToken)}"
    | .ident => addCurrToken
    | .string => addCurrToken
    | .comment => throw $ IO.userError s!"TPTP.parse.finalizeToken :: Cannot finalize comment"
    setStatus .default

def peek? : TokenizerM (Option Char) := do
  let st ← get
  if st.pos < st.input.length then
    return some (st.input.get ⟨st.pos⟩)
  else
    return none

def tokenizeAux : TokenizerM Unit := do
  let st ← get
  let input := st.input
  while (← get).pos < input.length do
    let st ← get
    let char := input.get ⟨st.pos⟩
    modify (fun st => { st with pos := st.pos + 1 })
    match ← getStatus with
    | .default =>
      if char.isWhitespace then
        finalizeToken
      else if char.isAlphanum || char == '$' then
        finalizeToken
        setStatus .ident
        addToCurrToken char
      else if (char == '-' || char == '+') &&
              match (← peek?) with
              | some c => c.isDigit
              | none => false then
        finalizeToken
        setStatus .ident
        addToCurrToken char
      else if char == '\'' then
        finalizeToken
        setStatus .string
      else if char == '%' then
        finalizeToken
        setStatus .comment
      else if tokenPrefixes.contains ((← getCurrToken).push char) then
        addToCurrToken char
      else if tokenPrefixes.contains (⟨[char]⟩) then
        finalizeToken
        addToCurrToken char
      else throw $ IO.userError s!"TPTP.parse :: Invalid token: {char}"
    | .ident =>
      if char.isWhitespace then
        finalizeToken
      else if char.isAlphanum || char == '_' then
        addToCurrToken char
      else
        finalizeToken
        addToCurrToken char
        setStatus .default
    | .string =>
      if char == '\'' then
        finalizeToken
      else
        addToCurrToken char
    | .comment =>
      if char == '\n' then
        setStatus .default
  finalizeToken

  def tokenize (s : String) : IO (Array Token) := do
    let initialState : State := { input := s, pos := 0, status := .default, currToken := "", res := #[] }
    let result ← tokenizeAux.run initialState
    return result.2.res

end Tokenizer

open Tokenizer
/- Pratt parser following `https://matklad.github.io/2020/04/13/simple-but-powerful-pratt-parsing.html`-/

structure State where
  tokens : Array Token
  curr   : Nat := 0
deriving Repr

abbrev ParserM := StateRefT State IO

def isEOF : ParserM Bool := do return (← get).curr ==  (← get).tokens.size

def peek : ParserM Token := do
  let i := (← get).curr
  let ts := (← get).tokens
  if i >= ts.size then throw $ IO.userError "TPTP.parse :: Unexpected end of file"
  return ts[i]!

def peek? : ParserM (Option Token) := do
  if ← isEOF then return none else return ← peek

def next : ParserM Token := do
  let c ← peek
  modify (fun (s : State) => {s with curr := s.curr + 1})
  return c

def infixBindingPower? : String → Option (Nat × Nat)
| "-->" => (10, 11)
| "|" | "&" | "<=>" | "=>" | "<=" | "<~>" | "~|" | "~&" | "@" => (60,61)
| "=" | "!=" => (90, 90)
| "*" => (41, 40)
| ">" => (51, 50)
| _ => none

def prefixBindingPower? : String → Option Nat
| "~" => some 70
| _ => none

def binderBindingPower? : String → Option Nat
| "!" | "!>" | "?" | "^" => some 70
| _ => none

def isPolyIL? : String → Bool
| "??" | "!!" | "=" => true
| _ => false

inductive Term where
  | mk : Token → List Term → Term
  deriving Inhabited, BEq, Repr

partial def Term.toString : Term → String
| .mk (Token.ident "list") [] =>
    "[]"
| .mk (Token.ident "list") args =>
    "[" ++ String.intercalate ", " (args.map Term.toString) ++ "]"
| .mk head [] =>
    head.toString
| .mk head args =>
    head.toString ++ " [" ++ String.intercalate ", " (args.map Term.toString) ++ "]"


instance : ToString Term where
  toString := Term.toString

def Term.func : Term → Token := fun ⟨n, _⟩ => n
def Term.args : Term → List Term := fun ⟨_, as⟩ => as

def parseToken (t : Token) : ParserM Unit := do
  let nextToken ← next
  if nextToken != t then throw $ IO.userError s!"TPTP.parse :: Expected '{t}', got '{repr nextToken}'"

def parseIdent : ParserM String := do
  let nextToken ← next
  let .ident id := nextToken
    | throw $ IO.userError s!"TPTP.parse :: Expected identifier, got '{repr nextToken}'"
  return id

partial def parseSep (sep : Token) (p : ParserM α) : ParserM (List α) := do
  let t ← p
  if (← peek?) == some sep then
    parseToken sep
    let l ← parseSep sep p
    return t :: l
  else
    return [t]

mutual
partial def parseTerm (minbp : Nat := 0) : ParserM Term := do
  let lhs ← parseLhs
  let res ← addOpAndRhs lhs minbp
  return res

partial def parseLhs : ParserM Term := do
  let nextToken ← next
  if let .ident _ := nextToken then
    if (← peek?) == some (.op "(") then
      parseToken (.op "(")
      let args ← parseSep (.op ",") (parseTerm 0)
      parseToken (.op ")")
      return Term.mk nextToken args
    else
      return Term.mk nextToken []
  else if nextToken == .op "(" then
    let p ← peek
    if (infixBindingPower? p.toString).isSome then
      -- support for (&) syntax
      let p ← next
      parseToken (.op ")")
      return ⟨p, []⟩
    else
      let lhs ← parseTerm 0
      parseToken (.op ")")
      return lhs
  else if nextToken == .op "[" then
    if (← peek?) == some (.op "]") then
      parseToken (.op "]")
      return Term.mk (Token.ident "list") []
    else
      let args ← parseSep (.op ",") (parseTerm 0)
      parseToken (.op "]")
      return Term.mk (Token.ident "list") args
  else if let some rbp := binderBindingPower? nextToken.toString then
    parseToken (.op "[")
    let vars ← parseSep (.op ",") parseTypeDecl
    parseToken (.op "]")
    parseToken (.op ":")
    let rhs ← parseTerm rbp
    return Term.mk nextToken (rhs :: vars)
  else if let some rbp := prefixBindingPower? nextToken.toString then
    if (← peek?) == .some (.op ")") then -- support for `(~)` syntax
      return Term.mk nextToken []
    else
      let rhs ← parseTerm rbp
      return Term.mk nextToken [rhs]
  else if isPolyIL? nextToken.toString && (← peek?) == .some (.op ")") then
    return Term.mk nextToken []
  else
    throw $ IO.userError s!"TPTP.parse :: Expected term, got '{repr nextToken}'"

partial def addOpAndRhs (lhs : Term) (minbp : Nat) : ParserM Term := do
  if ← isEOF then
    return lhs
  else
    let op ← peek
    let some (lbp, rbp) := infixBindingPower? op.toString
      | return lhs
    if lbp < minbp then
      return lhs
    else
      let op ← next
      let rhs ← parseTerm rbp
      return ← addOpAndRhs (Term.mk op [lhs, rhs]) minbp

partial def parseTypeDecl : ParserM Term := do
  let ident ← parseIdent
  if (← peek?) == some (.op ":") then
    parseToken (.op ":")
    let ty ← parseTerm
    return Term.mk (.ident ident) [ty]
  else
    return Term.mk (.ident ident) []
end

/--
  <thf_atom_typing>
  <tff_atom_typing>
-/
partial def parseAtomTyping : ParserM Term := do
  if (← peek?) == .some (.op "(") then
    parseToken (.op "(")
    let decl ← parseAtomTyping
    parseToken (.op ")")
    return decl
  else
    parseTypeDecl

structure Command where
  cmd : String
  args : List Term
deriving Inhabited, BEq

def Command.toString : Command → String
| .mk cmd args => cmd ++ "(" ++ String.intercalate ", " (args.map Term.toString) ++ ")"

instance : ToString Command where
  toString := Command.toString

def parseCommand : ParserM Command := do
  let cmd ← parseIdent
  match cmd with
  | "thf" | "tff" | "cnf" | "fof" =>
    parseToken (.op "(")
    let name ← parseIdent
    parseToken (.op ",")
    let kind ← parseIdent
    parseToken (.op ",")
    let val ← match kind with
    | "type" => parseAtomTyping
    | _ => parseTerm
    let mut source : Option Term := none
    if (← peek?) == some (.op ",") then
      parseToken (.op ",")
      source ← parseTerm
    parseToken (.op ")")
    parseToken (.op ".")
    if source.isSome then
      return ⟨cmd, [Term.mk (.ident name) [], Term.mk (.ident kind) [], val, source.get! ]⟩
    else
      return ⟨cmd, [Term.mk (.ident name) [], Term.mk (.ident kind) [], val]⟩
  | "include" =>
    parseToken (.op "(")
    let str ← parseIdent
    parseToken (.op ")")
    parseToken (.op ".")
    return ⟨cmd, [Term.mk (.ident str) []]⟩
  | _ => throw $ IO.userError s!"Command '{cmd}' not supported"

partial def parseCommands : ParserM (List Command) := do
  if ← isEOF
  then return []
  else
    let c ← parseCommand
    return c :: (← parseCommands)

def parse (s : String) : IO (Array Command) := do
  let tokens ← Tokenizer.tokenize s
  let res ← parseCommands.run {tokens}
  return (Array.mk res.fst)

open Embedding.Lam in
def ident2LamSort (s : String) : Option LamSort :=
  match s with
  | "s_nat"    => .some (.base .nat)
  | "s_int"    => .some (.base .int)
  | "s_string" => .some (.base .string)
  | "s_empty"  => .some (.base .empty)
  | _ =>
    if s.take 3 == "s_a" then
      match (s.drop 3).toNat? with
      | .some n => .some (.atom n)
      | .none => .none
    else if s.take 4 == "s_bv" then
      match (s.drop 4).toNat? with
      | .some n => .some (.base (.bv n))
      | .none   => .none
    else
      .none

open Embedding.Lam in
def ident2NatConst (s : String) : Option NatConst :=
  match s with
  | "t_nadd" => .some .nadd
  | "t_nsub" => .some .nsub
  | "t_nmul" => .some .nmul
  | "t_ndiv" => .some .ndiv
  | "t_nmod" => .some .nmod
  | "t_nle"  => .some .nle
  | "t_nlt"  => .some .nlt
  | "t_nmax" => .some .nmax
  | "t_nmin" => .some .nmin
  | _ =>
    match s.take 9 with
    | "t_natVal_" =>
      match (s.drop 9).toNat? with
      | .some n => .some (.natVal n)
      | .none   => .none
    | _ => .none

open Embedding.Lam in
def ident2StringConst (s : String) : Option StringConst :=
  match s with
  | "t_slength"   => .some .slength
  | "t_sapp"      => .some .sapp
  | "t_sle"       => .some .sle
  | "t_slt"       => .some .slt
  | "t_sprefixof" => .some .sprefixof
  | "t_srepall"   => .some .srepall
  | _ =>
    let foldFn (x : Option String) (y : String) : Option String :=
      match x, y.toNat? with
      | .some l, .some y' => .some (l.push (Char.ofNat y'))
      | _,       _        => .none
    match s.take 9, (((s.drop 9).splitOn "d").drop 1).foldl foldFn (.some "") with
    | "t_strVal_", .some s => .some (.strVal s)
    | _,         _       => .none

open Embedding.Lam in
def ident2IntConst (s : String) : Option IntConst :=
  match s with
  | "t_iofNat"   => .some .iofNat
  | "t_inegSucc" => .some .inegSucc
  | "t_ineg"     => .some .ineg
  | "t_iabs"     => .some .iabs
  | "t_iadd"     => .some .iadd
  | "t_isub"     => .some .isub
  | "t_imul"     => .some .imul
  | "t_idiv"     => .some .idiv
  | "t_imod"     => .some .imod
  | "t_iediv"    => .some .iediv
  | "t_iemod"    => .some .iemod
  | "t_ile"      => .some .ile
  | "t_ilt"      => .some .ilt
  | "t_imax"     => .some .imax
  | "t_imin"     => .some .imin
  | _ => .none

open Embedding.Lam in
def ident2BitVecConst (s : String) : Option BitVecConst :=
  match s.take 7 with
  | "t_bvVal" =>
    match (s.drop 7).splitOn "_" with
    | ["", ns, is] =>
      match ns.toNat?, is.toNat? with
      | .some n, .some i => .some (.bvVal n i)
      | _,       _       => .none
    | _ => .none
  | "t_bvofN" =>
    match s.take 10 == "t_bvofNat_", (s.drop 10).toNat? with
    | true, .some n => .some (.bvofNat n)
    | _,    _       => .none
  | "t_bvtoN" =>
    match s.take 10 == "t_bvtoNat_", (s.drop 10).toNat? with
    | true, .some n => .some (.bvtoNat n)
    | _,    _       => .none
  | "t_bvofI" =>
    match s.take 10 == "t_bvofInt_", (s.drop 10).toNat? with
    | true, .some n => .some (.bvofInt n)
    | _,    _       => .none
  | "t_bvtoI" =>
    match s.take 10 == "t_bvtoInt_", (s.drop 10).toNat? with
    | true, .some n => .some (.bvtoInt n)
    | _,    _       => .none
  | "t_bvmsb" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvmsb n)
    | _,   _       => .none
  | "t_bvadd" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvadd n)
    | _,   _       => .none
  | "t_bvsub" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvsub n)
    | _,   _       => .none
  | "t_bvneg" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvneg n)
    | _,   _       => .none
  | "t_bvabs" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvabs n)
    | _,   _       => .none
  | "t_bvmul" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvmul n)
    | _,   _       => .none
  | "t_bvudi" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvudiv_", .some n => .some (.bvudiv n)
    | _,           _       => .none
  | "t_bvure" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvurem_", .some n => .some (.bvurem n)
    | _,           _       => .none
  | "t_bvsdi" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvsdiv_", .some n => .some (.bvsdiv n)
    | _,           _       => .none
  | "t_bvsre" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvsrem_", .some n => .some (.bvsrem n)
    | _,           _       => .none
  | "t_bvsmo" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvsmod_", .some n => .some (.bvsmod n)
    | _,           _       => .none
  | "t_bvult" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvult n)
    | _,   _       => .none
  | "t_bvule" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvule n)
    | _,   _       => .none
  | "t_bvslt" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvslt n)
    | _,   _       => .none
  | "t_bvsle" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvsle n)
    | _,   _       => .none
  | "t_bvand" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvand n)
    | _,   _       => .none
  | "t_bvor_" =>
    match (s.drop 8).toNat? with
    | .some n => .some (.bvor n)
    | _       => .none
  | "t_bvxor" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvxor n)
    | _,   _       => .none
  | "t_bvnot" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvnot n)
    | _,   _       => .none
  | "t_bvshl" =>
    match s.get ⟨7⟩, (s.drop 8).toNat? with
    | '_', .some n => .some (.bvshl n)
    | _,   _       => .none
  | "t_bvlsh" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvlshr_", .some n => .some (.bvlshr n)
    | _,           _       => .none
  | "t_bvash" =>
    match s.take 9, (s.drop 8).toNat? with
    | "t_bvashr_", .some n => .some (.bvashr n)
    | _,           _       => .none
  | "t_bvsmt" =>
    match (s.drop 7).take 4 with
    | "shl_" =>
      match (s.drop 11).toNat? with
      | .some n => .some (.bvsmtshl n)
      | .none   => .none
    | _ =>
      match (s.drop 7).take 5, (s.drop 12).toNat? with
      | "lshr", .some n => .some (.bvsmtlshr n)
      | "ashr", .some n => .some (.bvsmtashr n)
      | _,      _       => .none
  | "t_bvapp" =>
    match s.take 11, (s.drop 11).splitOn "_" with
    | "t_bvappend_", [ns, ms] =>
      match ns.toNat?, ms.toNat? with
      | .some n, .some m => .some (.bvappend n m)
      | _,       _       => .none
    | _,             _        => .none
  | "t_bvext" =>
    match s.take 12, (s.drop 12).splitOn "_" with
    | "t_bvextract_", [ns, hs, ls] =>
      match ns.toNat?, hs.toNat?, ls.toNat? with
      | .some n, .some h, .some l => .some (.bvextract n h l)
      | _,       _,       _       => .none
    | _,              _            => .none
  | "t_bvrep" =>
    match s.take 11, (s.drop 11).splitOn "_" with
    | "t_bvrepeat_", [ws, is] =>
      match ws.toNat?, is.toNat? with
      | .some w, .some i => .some (.bvrepeat w i)
      | _,       _       => .none
    | _,             _        => .none
  | "t_bvzer" =>
    match s.take 15, (s.drop 15).splitOn "_" with
    | "t_bvzeroExtend_", [ws, vs] =>
      match ws.toNat?, vs.toNat? with
      | .some w, .some v => .some (.bvzeroExtend w v)
      | _,       _       => .none
    | _,             _        => .none
  | "t_bvsig" =>
    match s.take 15, (s.drop 15).splitOn "_" with
    | "t_bvsignExtend_", [ws, vs] =>
      match ws.toNat?, vs.toNat? with
      | .some w, .some v => .some (.bvsignExtend w v)
      | _,       _       => .none
    | _,             _        => .none
  | _ => .none

open Embedding.Lam in
inductive LamConstr where
  | error : String → LamConstr
  | kind  : LamConstr
  | sort  : LamSort → LamConstr
  | term  : LamSort → LamTerm → LamConstr
  deriving Inhabited, Hashable, BEq

def LamConstr.toString : LamConstr → String
| .error s => s!"error {s}"
| .kind    => "kind"
| .sort s  => s!"sort {s}"
| .term s t => s!"term {t} : {s}"

instance : ToString LamConstr where
  toString := LamConstr.toString

open Embedding.Lam in
structure ParsingInfo where
  lamVarTy     : Array LamSort
  lamEVarTy    : Array LamSort
  proverSkolem : Std.HashMap String (LamSort × Nat) := {}
  skolemExpr   : Array Expr := #[]

open Embedding.Lam in
def ParsingInfo.toLamTyVal (pi : ParsingInfo) : LamTyVal :=
  ⟨fun n => pi.lamVarTy.getD n (.base .prop),
   fun _ => .base .prop,
   fun n => pi.lamEVarTy.getD n (.base .prop)⟩

open Embedding.Lam in
def ParsingInfo.addSkolem (pi : ParsingInfo) (name : String) (s : LamSort) : MetaM ParsingInfo := do
  let newPi : ParsingInfo := {
    pi with
    proverSkolem := pi.proverSkolem.insert name (s, pi.proverSkolem.size),
    skolemExpr := pi.skolemExpr.push (← Meta.mkFreshExprMVar none .natural (Name.str .anonymous name))
  }
  return newPi

open Embedding.Lam in
def LamConstr.ofBaseTerm (pi : ParsingInfo) (b : LamBaseTerm) : LamConstr :=
  .term (b.lamCheck pi.toLamTyVal) (.base b)

open Embedding.Lam in
def ident2LamConstr (pi : ParsingInfo) (s : String) : LamConstr :=
  match pi.proverSkolem.get? s with
  | .some (s, n) => .term s (.etom (n + pi.lamEVarTy.size))
  | .none =>
    match s.get ⟨0⟩ with
    | 's' =>
      match ident2LamSort s with
      | .some b => .sort b
      | _       => .error s!"Unknown identifier {s}"
    | 't' =>
      match s.take 3 with
      | "t_a" =>
        match (s.drop 3).toNat? with
        | .some n =>
          match pi.lamVarTy[n]? with
          | .some s => .term s (.atom n)
          | .none => .error s!"Unknown atom {n}"
        | .none   => .error s!"Unknown identifier {s}"
      | "t_e" =>
        match (s.drop 3).toNat? with
        | .some n =>
          match pi.lamEVarTy[n]? with
          | .some s => .term s (.etom n)
          | .none   => .error s!"Unknown etom {n}"
        | .none   => .error s!"Unknown identifier {s}"
      | "t_n" =>
        match ident2NatConst s with
        | .some n => .term n.lamCheck (.base (.ncst n))
        | .none   => .error s!"Unknown identifier {s}"
      | "t_i" =>
        match ident2IntConst s with
        | .some i => .term i.lamCheck (.base (.icst i))
        | .none   => .error s!"Unknown identifier {s}"
      | "t_s" =>
        match ident2StringConst s with
        | .some s => .term s.lamCheck (.base (.scst s))
        | .none   => .error s!"Unknown identifier {s}"
      | "t_b" =>
        match ident2BitVecConst s with
        | .some bv => .term bv.lamCheck (.base (.bvcst bv))
        | .none   => .error s!"Unknown identifier {s}"
      | _ => .error s!"Unknown identifier {s}"
    | _   => .error s!"Unknown identifier {s}"

open Embedding.Lam in
/-- This function is only for zipperposition's output -/
partial def term2LamTerm (pi : ParsingInfo) (t : Term) (lctx : Std.HashMap String (Nat × LamSort) := {}) : LamConstr :=
  match t with
  | ⟨.ident "$i", []⟩ => .error "Does not have iota"
  | ⟨.ident "$tType", []⟩ => .kind
  | ⟨.ident "$o", []⟩ => .sort (.base .prop)
  | ⟨.ident "$true", []⟩ => .term (.base .prop) (.base .trueE)
  | ⟨.ident "$false", []⟩ => .term (.base .prop) (.base .falseE)
  | ⟨.ident ids, as⟩ =>
    let head :=
      match deBruijnAndSort? lctx ids with
      | .some (db, s) => .term s (.bvar db)
      | .none => ident2LamConstr pi ids
    match as with
    | .nil => head
    | .cons _ _ => lamConstrMkAppN head (as.map (term2LamTerm pi · lctx))
  | ⟨.op "!", body :: var :: tail⟩ =>
    match processVar pi var lctx with
    | .some (name, s) =>
      match term2LamTerm pi ⟨.op "!", body :: tail⟩ (lctx.insert name (lctx.size, s)) with
      | .term (.base .prop) body => .term (.base .prop) (.mkForallE s body)
      | r => .error s!"Unexpected term {t} produces ({r})"
    | r => .error s!"Unexpected term {t} produces ({r})"
  | ⟨.op "!>", body :: var :: tail⟩ =>
    match processVar pi var lctx with
    | .some (name, s) =>
      match term2LamTerm pi ⟨.op "!>", body :: tail⟩ (lctx.insert name (lctx.size, s)) with
      | .term (.base .prop) body => .term (.base .prop) (.mkForallEF s body)
      | r => .error s!"Unexpected term {t} produces ({r})"
    | r => .error s!"Unexpected term {t} produces ({r})"
  | ⟨.op "^", body :: var :: tail⟩ =>
    match processVar pi var lctx with
    | .some (name, s) =>
      match term2LamTerm pi ⟨.op "^", body :: tail⟩ (lctx.insert name (lctx.size, s)) with
      | .term resTy body => .term (.func s resTy) (.lam s body)
      | r => .error s!"Unexpected term {t} produces ({r})"
    | r => .error s!"Unexpected term {t} produces ({r})"
  | ⟨.op "?", body :: var :: tail⟩ =>
    match processVar pi var lctx with
    | .some (name, s) =>
      match term2LamTerm pi ⟨.op "?", body :: tail⟩ (lctx.insert name (lctx.size, s)) with
      | .term (.base .prop) body => .term (.base .prop) (.mkExistE s body)
      | r => .error s!"Unexpected term {t} produces ({r})"
    | r => .error s!"Unexpected term {t} produces ({r})"
  | ⟨.op "!", body :: []⟩ | ⟨.op "!>", body :: []⟩ | ⟨.op "^", body :: []⟩ | ⟨.op "?", body :: []⟩ =>
    term2LamTerm pi body lctx
  | ⟨.op "~", [a]⟩     =>
    match term2LamTerm pi a lctx with
    | .term (.base .prop) la => .term (.base .prop) (.mkNot la)
    | r => .error s!"Unexpected term {t} produces ({r})"
  | ⟨.op "|", [a,b]⟩   =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb => .term (.base .prop) (.mkOr la lb)
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "&", [a,b]⟩   =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb => .term (.base .prop) (.mkAnd la lb)
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "<=>", [a,b]⟩ =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb => .term (.base .prop) (.mkIff la lb)
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "!=", [a,b]⟩  =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term s₁ la, .term s₂ lb =>
      match s₁.beq s₂ with
      | true => .term (.base .prop) (.mkNot (.mkEq s₁ la lb))
      | false => .error s!"Application type mismatch in {t}"
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "=", [a,b]⟩   =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term s₁ la, .term s₂ lb =>
      match s₁.beq s₂ with
      | true => .term (.base .prop) (.mkEq s₁ la lb)
      | false => .error s!"Application type mismatch in {t}"
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "~|", [a,b]⟩  =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb =>
      .term (.base .prop) (.mkNot (.mkOr la lb))
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "~&", [a,b]⟩  =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb =>
      .term (.base .prop) (.mkNot (.mkAnd la lb))
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "<~>", [a,b]⟩ =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb =>
      .term (.base .prop) (.mkNot (.mkIff la lb))
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "@", [a,b]⟩   =>
    match term2LamTerm pi b lctx with
    | .term argTy' lb =>
      match isPolyIL? a.toString with
      | true =>
        if a.toString == "=" then
          .term (.base .prop) (.app argTy' (.base (.eq argTy')) lb)
        else
          match argTy' with
          | .func domTy (.base .prop) =>
            let b := if a.toString == "??" then .existE domTy else .forallE domTy
            .term (.base .prop) (.app argTy' (.base b) lb)
          | _ => .error s!"Invalid argument type for {a}"
      | false =>
        match term2LamTerm pi a lctx with
        | .term fnTy la =>
          match fnTy with
          | .func argTy resTy =>
            match argTy.beq argTy' with
            | true => .term resTy (.app argTy la lb)
            | false => .error s!"Application type mismatch ({fnTy} applied to {argTy'}) in {t}"
          | _ => .error s!"Non-function type {fnTy} applied to arg in {t}"
        | r => .error s!"Unexpected term {t} produces ({r}) at appFn"
    | r => .error s!"Unexpected term {t} produces ({r}) at appArg"
  | ⟨.op "=>", [a,b]⟩ | ⟨.op "<=", [b,a]⟩ =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .term (.base .prop) la, .term (.base .prop) lb => .term (.base .prop) (.mkImp la lb)
    | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "~", []⟩   => .ofBaseTerm pi .not
  | ⟨.op "|", []⟩   => .ofBaseTerm pi .or
  | ⟨.op "&", []⟩   => .ofBaseTerm pi .and
  | ⟨.op "<=>", []⟩ => .ofBaseTerm pi .iff
  | ⟨.op "!=", []⟩  => .error s!"Unapplied (!=), cannot infer type"
  | ⟨.op "=", []⟩   => .error s!"Unapplied (=), cannot infer type"
  | ⟨.op "!!", []⟩  => .error s!"Unapplied (!!), cannot infer type"
  | ⟨.op "??", []⟩  => .error s!"Unapplied (??), cannot infer type"
  | ⟨.op "~|", []⟩  => .term (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    (.lam (.base .prop) (.lam (.base .prop) (.mkNot (.mkOr (.bvar 1) (.bvar 0)))))
  | ⟨.op "~&", []⟩  => .term (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    (.lam (.base .prop) (.lam (.base .prop) (.mkNot (.mkAnd (.bvar 1) (.bvar 0)))))
  | ⟨.op "<~>", []⟩ => .term (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    (.lam (.base .prop) (.lam (.base .prop) (.mkNot (.mkIff (.bvar 1) (.bvar 0)))))
  | ⟨.op "=>", []⟩  => .ofBaseTerm pi .imp
  | ⟨.op "<=", []⟩  => .term (.func (.base .prop) (.func (.base .prop) (.base .prop)))
    (.lam (.base .prop) (.lam (.base .prop) (.mkImp (.bvar 0) (.bvar 1))))
  | ⟨.op ">", [⟨.op "*", [a, b]⟩, c]⟩   =>
    term2LamTerm pi ⟨.op ">", [a, ⟨.op ">", [b, c]⟩]⟩ lctx
  | ⟨.op ">", [a, b]⟩ =>
    match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
    | .sort sa, .sort sb => .sort (.func sa sb)
    | _, r => .error s!"Unexpected term {t} produces ({r})"
  -- | ⟨.op "-->", [a, b]⟩ =>
  --   match term2LamTerm pi a lctx, term2LamTerm pi b lctx with
  --   | .term (.base .prop) la, .term (.base .prop) lb =>
  --       .term (.base .prop) (.mkImp la lb)
  --   | r₁, r₂ => .error s!"Unexpected term {t} produces ({r₁}) and ({r₂})"
  | _ => .error s!"term2LamTerm :: Could not translate to Lean Expr: {t}"
where
  processVar (pi : ParsingInfo) (var : Term) (lctx : Std.HashMap String (Nat × LamSort)) : Option (String × LamSort) :=
    match var with
    | ⟨.ident v, ty⟩ =>
      match ty with
      | [ty] =>
        match term2LamTerm pi ty lctx with
        | .sort s => .some (v, s)
        | _ => .none
      | _ => .none
    | _ => .none
  deBruijnAndSort? (lctx : Std.HashMap String (Nat × LamSort)) (id : String) : Option (Nat × LamSort) :=
    match lctx.get? id with
    | .some (n, s) => (lctx.size - 1 - n, s)
    | .none => none
  lamConstrMkAppN (head : LamConstr) (args : List LamConstr) :=
    match head, args with
    | .term s₁ t₁, .nil => .term s₁ t₁
    | .term s₁ t₁, .cons (.term s₂ t₂) tail =>
      match s₁ with
      | .func argTy resTy =>
        match argTy.beq s₂ with
        | true => lamConstrMkAppN (.term resTy (.app s₂ t₁ t₂)) tail
        | false => .error s!"term2LamTerm :: Application type ({s₁} applied to {s₂}) mismatch in lamConstrMkAppN, `{head}` `{args}`"
      | _ => .error s!"term2LamTerm :: Non-function head `{head}` applied to argument"
    | _, _ => .error s!"term2LamTerm :: Unexpected input `{head}`, `{args}` to lamConstrMkAppN"

open Embedding.Lam in
/--
  Turn TSTP term into LamSort/LamTerm
  This function is only for zipperposition's output
-/
def getProof (lamVarTy lamEVarTy : Array LamSort) (cmds : Array Command) : MetaM (Array LamTerm) := do
  let mut ret := #[]
  let mut pi : ParsingInfo := ⟨lamVarTy, lamEVarTy, {}, #[]⟩
  for ⟨cmd, args⟩ in cmds do
    match cmd with
    | "thf" | "tff" | "cnf" | "fof" =>
      match args with
      | [⟨.ident name, []⟩, ⟨.ident kind, _⟩, val] =>
        if kind != "type" then
          match term2LamTerm pi val with
          | .term (.base .prop) t =>
            ret := ret.push t
          | .error e => throwError (decl_name% ++ " :: " ++ e)
          | lc => throwError "{decl_name%} :: Unexpected LamConstr {lc}, expected term"
        else
          match val with
          | ⟨.ident name, [ty]⟩ =>
            -- In zipperposition, skolems start with `sk_` or `#sk_`
            if name.take 3 == "sk_" || name.take 3 == "#sk" then
              match term2LamTerm pi ty with
              | .sort s => pi ← pi.addSkolem name s
              | lc => throwError "{decl_name%} :: Unexpected LamConstr {lc}, expected sort"
            else
              continue
          | _ => continue
      | _ => continue
    | "include" => throwError "{decl_name%} :: `include` should not occur in proof output of TPTP solvers"
    | _ => throwError "{decl_name%} :: Unknown command {cmd}"
  return ret

/-- Returns the unsat core of an array of TSTP steps -/
def unsatCore (cmds : Array Command) : MetaM (Array Nat) := do
  let mut res := #[]
  for ⟨_, args⟩ in cmds do
    if args.length > 1 then
      if let ⟨.ident kind, []⟩ := args[1]! then
        if ["axiom", "conjecture", "negated_conjecture"].contains kind then
          if let ⟨.ident id, []⟩ := args[0]! then
            if id.take 4 == "fact" then
              if let .some n := (id.drop 4).toNat? then
                res := res.push n
  return res


/- #####################################
  SC-TPTP related code
##################################### -/


/-- Helper to print Parser.TPTP.Term tree -/
partial def termTreeString (t : Term) (depth : Nat := 0) : String :=
  let indent := String.join (List.replicate depth "  ")
  match t with
  | ⟨.ident s, []⟩ => s!"{indent}[ident {s}]"
  | ⟨.ident s, args⟩ => s!"{indent}[ident {s}]({String.intercalate ", " (args.map termTreeString)})"
  | ⟨.op s, []⟩ => s!"{indent}[op {s}]"
  | ⟨.op s, args⟩    => s!"{indent}[op {s}]({String.intercalate ", " (args.map termTreeString)})"


open Embedding.Lam in
partial def term2LamTermSCTPTP (pi : ParsingInfo) (t : Term) (lctx : Std.HashMap String (Nat × LamSort) := {}) : LamConstr :=
  match t with
  | ⟨.ident "$true", []⟩ => .term (.base .prop) (.base .trueE)
  | ⟨.ident "$false", []⟩ => .term (.base .prop) (.base .falseE)
  | ⟨.ident "app", args⟩ =>
    match args with
    | [f, a] =>
      match term2LamTermSCTPTP pi f lctx, term2LamTermSCTPTP pi a lctx with
      | .term s₁ f, .term _ a =>
        match s₁ with
        | .func argTy resTy => .term resTy (.app argTy f a)
        | _ => .error s!"term2LamTermSCTPTP :: Non-function head `{f}` applied to argument"
      | r, p => .error s!"`app`: Unexpected term {t} produces ({r}) and ({p})"
    | _ => .error s!"`app`: Unexpected term {t}"
  | ⟨.ident ids, as⟩ =>
    let head :=
      match deBruijnAndSort? lctx ids with
      | .some (db, s) => .term s (.bvar db)
      | .none => ident2LamConstr pi ids
    match as with
    | .nil => head
    | .cons _ _ => lamConstrMkAppN head (as.map (term2LamTermSCTPTP pi · lctx))
  | ⟨.op "!", body :: var :: tail⟩ =>
    match processVar pi var lctx with
    | .some (name, s) =>
      match term2LamTermSCTPTP pi ⟨.op "!", body :: tail⟩ (lctx.insert name (lctx.size, s)) with
      | .term _ body => .term (.base .prop) (.mkForallEF s body)
      | r => .error s!"`!1`: Unexpected term {t} (body: {termTreeString body}, var: {termTreeString var}) produces ({r})"
    | r => .error s!"`!2`: Unexpected term {t} (body: {termTreeString body}, var: {termTreeString var}) produces ({r})"
  | ⟨.op "?", body :: var :: tail⟩ =>
    match processVar pi var lctx with
    | .some (name, s) =>
      match term2LamTermSCTPTP pi ⟨.op "?", body :: tail⟩ (lctx.insert name (lctx.size, s)) with
      | .term _ body => .term (.base .prop) (.mkExistEF s body)
      | r => .error s!"`?1`: Unexpected term {t} (body: {termTreeString body}, var: {termTreeString var}) produces ({r})"
    | r => .error s!"`?2`: Unexpected term {t} (body: {termTreeString body}, var: {termTreeString var}) produces ({r})"
  | ⟨.op "^", body :: var :: tail⟩ =>
    match processVar pi var lctx with
    | .some (name, s) =>
      match term2LamTermSCTPTP pi ⟨.op "^", body :: tail⟩ (lctx.insert name (lctx.size, s)) with
      | .term resTy body => .term (.func s resTy) (.lam s body)
      | r => .error s!"Unexpected term {t} produces ({r})"
    | r => .error s!"Unexpected term {t} produces ({r})"
  | ⟨.op "!", body :: []⟩ | ⟨.op "?", body :: []⟩ | ⟨.op "^", body :: []⟩ =>
    term2LamTermSCTPTP pi body lctx
  | ⟨.op "~", [a]⟩     =>
    match term2LamTermSCTPTP pi a lctx with
    | .term _ la => .term (.base .prop) (.mkNot la)
    | r => .error s!"`~`: Unexpected term {t} produces ({r})"
  | ⟨.op "|", [a,b]⟩   =>
    match term2LamTermSCTPTP pi a lctx, term2LamTermSCTPTP pi b lctx with
    | .term _ la, .term (.base .prop) lb => .term (.base .prop) (.mkOr la lb)
    | r₁, r₂ => .error s!"`|`: Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "&", [a,b]⟩   =>
    match term2LamTermSCTPTP pi a lctx, term2LamTermSCTPTP pi b lctx with
    | .term _ la, .term (.base .prop) lb => .term (.base .prop) (.mkAnd la lb)
    | r₁, r₂ => .error s!"`&`: Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "<=>", [a,b]⟩ =>
    match term2LamTermSCTPTP pi a lctx, term2LamTermSCTPTP pi b lctx with
    | .term _ la, .term _ lb => .term (.base .prop) (.mkIff la lb)
    | r₁, r₂ => .error s!"`<=>`: Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "!=", [a,b]⟩  =>
    match term2LamTermSCTPTP pi a lctx, term2LamTermSCTPTP pi b lctx with
    | .term (.base .int) la, .term s₂ lb => .term (.base .prop) (.mkNot (.mkEq s₂ la lb))
    | .term s₁ la, .term _ lb            => .term (.base .prop) (.mkNot (.mkEq s₁ la lb))
    | r₁, r₂ => .error s!"`!=`: Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "=", [a,b]⟩   =>
    match term2LamTermSCTPTP pi a lctx, term2LamTermSCTPTP pi b lctx with
    | .term (.base .int) la, .term s₂ lb => .term (.base .prop) (.mkEq s₂ la lb)
    | .term s₁ la, .term _ lb            => .term (.base .prop) (.mkEq s₁ la lb)
    | r₁, r₂ => .error s!"`=`: Unexpected term {t} produces ({r₁}) and ({r₂})"
  | ⟨.op "=>", [a,b]⟩ | ⟨.op "<=", [b,a]⟩ =>
    match term2LamTermSCTPTP pi a lctx, term2LamTermSCTPTP pi b lctx with
    | .term _ la, .term _ lb => .term (.base .prop) (.mkImp la lb)
    | r₁, r₂ => .error s!"`=>`: Unexpected term {t} produces ({r₁}) and ({r₂})"
  | _ => .error s!"term2LamTermSCTPTP :: Could not translate to Lean Expr: {termTreeString t}"
where
  processVar (pi : ParsingInfo) (var : Term) (lctx : Std.HashMap String (Nat × LamSort)) : Option (String × LamSort) :=
    match var with
    | ⟨.ident v, []⟩ =>
      match term2LamTermSCTPTP pi var lctx with
      | .term s _ => .some (v, s)
      | .sort s => .some (v, s)
      | _ => .some (v, .base .int) -- TODO: this is a hack to indicate that we don't know the type and that it should be inferred
    | _ => .none
  deBruijnAndSort? (lctx : Std.HashMap String (Nat × LamSort)) (id : String) : Option (Nat × LamSort) :=
    match lctx.get? id with
    | .some (n, s) => (lctx.size - 1 - n, s)
    | .none => none
  lamConstrMkAppN (head : LamConstr) (args : List LamConstr) :=
    match head, args with
    | .term s₁ t₁, .nil => .term s₁ t₁
    | .term s₁ t₁, .cons (.term s₂ t₂) tail =>
      match s₁ with
      | .func argTy resTy =>
        match argTy.beq s₂ with
        | true => lamConstrMkAppN (.term resTy (.app s₂ t₁ t₂)) tail
        | false => .error s!"term2LamTermSCTPTP :: Application type ({s₁} applied to {s₂}) mismatch in lamConstrMkAppN, `{head}` `{args}`"
      | _ => .error s!"term2LamTermSCTPTP :: Non-function head `{head}` applied to argument"
    | _, _ => .error s!"term2LamTermSCTPTP :: Unexpected input `{head}`, `{args}` to lamConstrMkAppN"


def resolveTypes (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars (← Core.betaReduce e)
  Meta.check e
  return e

open Lam2D LamReif in
def lamTerm2Expr (t : Embedding.Lam.LamTerm) (pi : ParsingInfo) : ReifM Expr := do
  let tyValMap := Std.HashMap.ofList ((← getTyVal).zipWithIndex.map (fun ((e, _), n) => (n, e))).toList
  let varValMap := Std.HashMap.ofList ((← getVarVal).zipWithIndex.map (fun ((e, _), n) => (n, e))).toList
  let etomValMap := Std.HashMap.ofList (pi.skolemExpr.zipWithIndex.map (fun (e, n) => (n, e))).toList
  resolveTypes (← interpLamTermAsUnliftedWithInference tyValMap varValMap etomValMap 0 t)


inductive InferenceRule where
-- Level 1
  | rightTrue     (i : Nat)
  | leftFalse     (i : Nat)
  | hyp           (i : Nat)
  | leftWeaken    (i : Nat)
  | rightWeaken   (i : Nat)
  | cut           (i : Nat)
  | leftAnd       (i : Nat)
  | leftOr        (i : Nat)
  | leftImplies   (i : Nat)
  | leftIff       (i : Nat)
  | leftNot       (i : Nat)
  | leftEx        (i : Nat) (y : String)
  | leftForall    (i : Nat) (t : Expr)
  | rightAnd      (i : Nat)
  | rightOr       (i : Nat)
  | rightImplies  (i : Nat)
  | rightIff      (i : Nat)
  | rightNot      (i : Nat)
  | rightEx       (i : Nat) (t : Expr)
  | rightForall   (i : Nat) (y : String)
  | rightRefl     (i : Nat)
  | rightSubstEq  (i : Nat) (backward : Bool) (P : Expr)
  | leftSubstEq   (i : Nat) (backward : Bool) (P : Expr)
  | rightSubstIff (i : Nat) (backward : Bool) (R : Expr)
  | leftSubstIff  (i : Nat) (backward : Bool) (R : Expr)
  | instFun       (F : String) (t : Expr)
  | instPred      (P : String) (phi : Expr)
  | rightEpsilon  (A : Expr) (x : String) (t : Expr)
  | leftEpsilon   (i : Nat) (y : String)

-- Level 2
  | congruence
  | leftHyp        (i : Nat)
  | leftNotAnd     (i : Nat)
  | leftNotOr      (i : Nat)
  | leftNotImplies (i : Nat)
  | leftNotIff     (i : Nat)
  | leftNotNot     (i : Nat)
  | leftNotEx      (i : Nat) (t : Expr)
  | leftNotAll     (i : Nat) (y : String)

-- Level 3
  | rightRelIff              (i : Nat)
  | rightSubstMulti          (i : List Nat) (P : Expr) (vars : List String)
  | leftSubstMulti           (i : List Nat) (P : Expr) (vars : List String)
  | rightSubstEqForallLocal  (i : Nat) (R : Expr) (Z : Expr)
  | rightSubstEqForall       (i : Nat) (R : Expr) (Z : Expr)
  | rightSubstIffForallLocal (i : Nat) (R : Expr) (Z : Expr)
  | rightSubstIffForall      (i : Nat) (R : Expr) (Z : Expr)
  | rightNnf                 (i : Nat) (j : Nat)
  | rightPrenex              (i : Nat) (j : Nat)
  | clausify                 (i : Nat)
  | elimIffRefl              (i : Nat)
  | res                      (i : Nat)
  | instMult                 (args : List (String × Expr))
deriving Inhabited, Repr

def InferenceRule.toMessageData : InferenceRule → MessageData
  -- Level 1
  | .rightTrue i         => m!"rightTrue [{i}]"
  | .leftFalse i         => m!"leftFalse [{i}]"
  | .hyp i               => m!"hyp [{i}]"
  | .leftWeaken i        => m!"leftWeaken [{i}]"
  | .rightWeaken i       => m!"rightWeaken [{i}]"
  | .cut i               => m!"cut [{i}]"
  | .leftAnd i           => m!"leftAnd [{i}]"
  | .leftOr i            => m!"leftOr [{i}]"
  | .leftImplies i       => m!"leftImplies [{i}]"
  | .leftIff i           => m!"leftIff [{i}]"
  | .leftNot i           => m!"leftNot [{i}]"
  | .leftEx i y          => m!"leftEx [{i}, {y}]"
  | .leftForall i t      => m!"leftForall [{i}, `{t}`]"
  | .rightAnd i          => m!"rightAnd [{i}]"
  | .rightOr i           => m!"rightOr [{i}]"
  | .rightImplies i      => m!"rightImplies [{i}]"
  | .rightIff i          => m!"rightIff [{i}]"
  | .rightNot i          => m!"rightNot [{i}]"
  | .rightEx i t         => m!"rightEx [{i}, `{t}`]"
  | .rightForall i y     => m!"rightForall [{i}, {y}]"
  | .rightRefl i         => m!"rightRefl [{i}]"
  | .rightSubstEq i b P  => m!"rightSubstEq [{i}, {b}, `{P}`]"
  | .leftSubstEq i b P   => m!"leftSubstEq [{i}, {b}, `{P}`]"
  | .rightSubstIff i b R => m!"rightSubstIff [{i}, {b}, `{R}`]"
  | .leftSubstIff i b R  => m!"leftSubstIff [{i}, {b}, `{R}`]"
  | .instFun F t         => m!"instFun [{F}, `{t}`]"
  | .instPred P phi      => m!"instPred [{P}, `{phi}`]"
  | .rightEpsilon A x t  => m!"rightEpsilon [{A}, {x}, `{t}`]"
  | .leftEpsilon i y     => m!"leftEpsilon [{i}, {y}]"

  -- Level 2
  | .congruence          => "congruence"
  | .leftHyp i           => m!"leftHyp [{i}]"
  | .leftNotAnd i        => m!"leftNotAnd [{i}]"
  | .leftNotOr i         => m!"leftNotOr [{i}]"
  | .leftNotImplies i    => m!"leftNotImplies [{i}]"
  | .leftNotIff i        => m!"leftNotIff [{i}]"
  | .leftNotNot i        => m!"leftNotNot [{i}]"
  | .leftNotEx i t       => m!"leftNotEx [{i}, `{t}`]"
  | .leftNotAll i y      => m!"leftNotAll [{i}, {y}]"

  -- Level 3
  | .rightRelIff i                  => m!"rightRelIff [{i}]"
  | .rightSubstMulti i P vars       => m!"rightSubstMulti [{i}, `{P}`, {vars}]"
  | .leftSubstMulti i P vars        => m!"leftSubstMulti [{i}, `{P}`, {vars}]"
  | .rightSubstEqForallLocal i R Z  => m!"rightSubstEqualForallLocal [{i}, `{R}`, {Z}]"
  | .rightSubstEqForall i R Z       => m!"rightSubstEqForall [{i}, `{R}`, {Z}]"
  | .rightSubstIffForallLocal i R Z => m!"rightSubstIffForallLocal [{i}, `{R}`, {Z}]"
  | .rightSubstIffForall i R Z      => m!"rightSubstIffForall [{i}, `{R}`, {Z}]"
  | .rightNnf i j                   => m!"rightNnf [{i} {j}]"
  | .rightPrenex i j                => m!"rightPrenex [{i} {j}]"
  | .clausify i                     => m!"clausify [{i}]"
  | .elimIffRefl i                  => m!"elimIffRefl [{i}]"
  | .res i                          => m!"res [{i}]"
  | .instMult args =>
      let argsStr := Lean.MessageData.joinSep (args.map (fun (x, y) => m!"{x}: {y}")) ", "
      m!"instMult [{argsStr}]"

instance : Lean.ToMessageData InferenceRule where
  toMessageData rule := InferenceRule.toMessageData rule

def parseBool (pt : Term) : Bool :=
  match pt with
  | Term.mk (Token.ident s) _ =>
    match s with
    | "true" => true
    | "false" => false
    | _   => panic! "parseBool: not a valid boolean"
  | _ => panic! "parseBool: unexpected term format"

def parseNat (pt : Term) : Nat :=
  match pt with
  | Term.mk (Token.ident s) _ =>
    match s.toNat? with
    | some n => n
    | none   => panic! "parseNat: not a valid numeral"
  | _ => panic! "parseNat: unexpected term format"

def parseListNat (pt : Term) : List Nat :=
  match pt with
  | Term.mk (Token.ident "list") args =>
    args.map fun arg =>
      match arg with
      | Term.mk (Token.ident s) _ =>
        match s.toNat? with
        | some n => n
        | none   => panic! s!"parseListNat: not a valid numeral: {s}"
      | _ => panic! s!"parseListNat: unexpected term format: {arg}"
  | Term.mk (Token.ident s) _ =>
    match s.toNat? with
    | some n => [n]
    | none   => panic! s!"parseListNat: not a valid numeral: {s}"
  | _ => panic! s!"parseListNat: unexpected term format: {pt}"

def parseParamString (pt : Term) : String :=
  match pt with
  | Term.mk (Token.ident s) _ => s
  | _ => panic! "parseParamString: unexpected term format"

def parseListString (pt : Term) : List String :=
  match pt with
  | Term.mk (Token.ident "list") args =>
    args.map fun arg =>
      match arg with
      | Term.mk (Token.ident s) _ => s
      | _ => panic! s!"parseListString: unexpected term format: {arg}"
  | Term.mk (Token.ident s) _ => [s]
  | _ => panic! s!"parseListString: unexpected term format: {pt}"

structure InferenceRecord where
  rule      : InferenceRule
  premises  : List String
deriving Inhabited, Repr

def InferenceRecord.toMessageData : InferenceRecord → MessageData
  | ⟨rule, premises⟩ =>
    let rule := InferenceRule.toMessageData rule
    let premises := MessageData.joinSep (premises.map (fun s => m!"{s}")) ", "
    m!"InferenceRecord [{rule}, {premises}]"

instance : ToMessageData InferenceRecord where
  toMessageData record := InferenceRecord.toMessageData record

-- method traversing a parsed term, and adding new variables to the parsing info for each unknown variable
partial def updateVars (pi : ParsingInfo) (t : Term) : LamReif.ReifM ParsingInfo := do
  match t with
  | ⟨.ident s, []⟩ =>
    match ident2LamConstr pi s with
    | .error _ => pi.addSkolem s (.base .int)
    | _ => pure pi
  | ⟨_, args⟩ =>
    let mut pi := pi
    for arg in args do
      pi := (← updateVars pi arg)
    pure pi

def term2Expr (pi : ParsingInfo) (t : Term) : LamReif.ReifM (Expr × ParsingInfo) := do
  let pi ← updateVars pi t
  match term2LamTermSCTPTP pi t {} with
  | .term _ t =>
    let e ← lamTerm2Expr t pi
    pure (e, pi)
  | .error e => throwError e
  | lc => throwError "Unexpected LamConstr {lc}, expected term"

def extractTerm (pi : ParsingInfo) (pt : Term) (vars : List String := []): LamReif.ReifM (Expr × ParsingInfo) :=
  match pt with
  | Term.mk (Token.ident "$fot") [inner]
  | Term.mk (Token.ident "$fof") [inner] =>
    let inner := if vars.isEmpty then inner else ⟨.op "^", inner :: vars.map (fun v => ⟨.ident v, []⟩)⟩
    term2Expr pi inner
  | _ => throwError "{decl_name%}: expected a $fot / $fof term but got {pt}"

open Embedding.Lam InferenceRule in
def parseInferenceRecord (t : Term) (pi : ParsingInfo) : LamReif.ReifM (InferenceRecord × ParsingInfo) := do
  let mut pi := pi
  match t with
  | Term.mk (Token.ident "inference") args =>
    if args.length < 3 then
      throwError "parseInferenceRecord: expected at least three arguments"
    else
      let ruleTerm     := args[0]!
      let paramTerm    := args[1]!
      let premisesTerm := args[2]!

      -- Extract params and check that paramTerm starts with "status(thm)"
      let params :=
        match paramTerm with
        | Term.mk (Token.ident "list") (first :: args) =>
          match first with
          | Term.mk (Token.ident "status") [statusArg] =>
            if statusArg.toString = "thm" then
              args
            else
              panic! s!"parseInferenceRecord: Expected status(thm) but got status({statusArg})"
          | _ => panic! "parseInferenceRecord: Expected first element of paramTerm to be status(thm)"
        | _ => panic! "parseInferenceRecord: Expected paramTerm to be a list (i.e. parsed from square brackets)"

      let premises : List String :=
        match premisesTerm with
        | Term.mk (Token.ident "list") args =>
          args.map fun arg =>
            match arg with
            | Term.mk (Token.ident s) _ => s
            | _ => panic! s!"parseInferenceRecord: unexpected premises term format: {arg}"
        | Term.mk (Token.ident s) _ => [s]
        | _ => panic! s!"parseInferenceRecord: unexpected premises term format: {premisesTerm}"

      let ruleName :=
        match ruleTerm with
        | Term.mk (Token.ident s) _ => s
        | _ => panic! s!"parseInferenceRecord: unexpected rule term format: {ruleTerm}"

      let rule : InferenceRule ←
        match ruleName with
        -- Level 1
        | "leftFalse"     => pure (leftFalse (parseNat params[0]!))
        | "rightTrue"     => pure (rightTrue (parseNat params[0]!))
        | "hyp"           => pure (hyp (parseNat (params[0]!)))
        | "leftWeaken"    => pure (leftWeaken (parseNat params[0]!))
        | "rightWeaken"   => pure (rightWeaken (parseNat params[0]!))
        | "cut"           => pure (cut (parseNat params[0]!))
        | "leftAnd"       => pure (leftAnd (parseNat params[0]!))
        | "leftOr"        => pure (leftOr (parseNat params[0]!))
        | "leftImplies"   => pure (leftImplies (parseNat params[0]!))
        | "leftIff"       => pure (leftIff (parseNat params[0]!))
        | "leftNot"       => pure (leftNot (parseNat params[0]!))
        | "leftEx"        => pure (leftEx (parseNat (params[0]!)) (parseParamString (params[1]!)))
        | "leftForall"    =>
          let (t, piloc) ← extractTerm pi params[1]!
          pi := piloc
          pure (leftForall (parseNat (params[0]!)) t)
        | "rightAnd"      => pure (rightAnd (parseNat params[0]!))
        | "rightOr"       => pure (rightOr (parseNat params[0]!))
        | "rightImplies"  => pure (rightImplies (parseNat params[0]!))
        | "rightIff"      => pure (rightIff (parseNat params[0]!))
        | "rightNot"      => pure (rightNot (parseNat params[0]!))
        | "rightEx"       =>
          let (t, piloc) ← extractTerm pi params[1]!
          pi := piloc
          pure (rightEx (parseNat (params[0]!)) t)
        | "rightForall"   => pure (rightForall (parseNat (params[0]!)) (parseParamString (params[1]!)))
        | "rightRefl"     => pure (rightRefl (parseNat params[0]!))
        | "rightSubst"    =>
          let (t, piloc) ← extractTerm pi params[2]! [parseParamString (params[3]!)]
          pi := piloc
          pure (rightSubstEq (parseNat (params[0]!)) (parseBool (params[1]!)) t)
        | "leftSubst"     =>
          let (t, piloc) ← extractTerm pi params[2]! [parseParamString (params[3]!)]
          pi := piloc
          pure (leftSubstEq (parseNat (params[0]!)) (parseBool (params[1]!)) t)
        | "rightSubstIff" =>
          let (t, piloc) ← extractTerm pi params[2]! [parseParamString (params[3]!)]
          pi := piloc
          pure (rightSubstIff (parseNat (params[0]!)) (parseBool (params[1]!)) t)
        | "leftSubstIff"  =>
          let (t, piloc) ← extractTerm pi params[2]! [parseParamString (params[3]!)]
          pi := piloc
          pure (leftSubstIff (parseNat (params[0]!)) (parseBool (params[1]!)) t)
        | "instFun"       =>
          let (t, piloc) ← extractTerm pi params[1]! [parseParamString (params[2]!)]
          pi := piloc
          pure (instFun (parseParamString params[0]!) t)
        | "instPred"      =>
          let (t, piloc) ← extractTerm pi params[1]! [parseParamString (params[2]!)]
          pi := piloc
          pure (instPred (parseParamString params[0]!) t)
        | "rightEpsilon"  =>
          let (t1, piloc) ← extractTerm pi params[0]!
          let (t2, piloc) ← extractTerm piloc params[0]!
          pi := piloc
          pure (rightEpsilon t1 (parseParamString params[1]!) t2)
        | "leftEpsilon"   => pure (leftEpsilon (parseNat params[0]!) (parseParamString params[1]!))

        -- Level 2
        | "congruence"     => pure congruence
        | "leftHyp"        => pure (leftHyp (parseNat (params[0]!)))
        | "leftNotAnd"     => pure (leftNotAnd (parseNat params[0]!))
        | "leftNotOr"      => pure (leftNotOr (parseNat params[0]!))
        | "leftNotImplies" => pure (leftNotImplies (parseNat params[0]!))
        | "leftNotIff"     => pure (leftNotIff (parseNat params[0]!))
        | "leftNotNot"     => pure (leftNotNot (parseNat params[0]!))
        | "leftNotEx"      =>
          let (t, piloc) ← extractTerm pi params[1]!
          pi := piloc
          pure (leftNotEx (parseNat (params[0]!)) t)
        | "leftNotAll"     => pure (leftNotAll (parseNat (params[0]!)) (parseParamString (params[1]!)))

        -- Level 3
        | "rightRelIff"              => pure (rightRelIff (parseNat params[0]!))
        | "rightSubstMulti"          =>
          let (t, piloc) ← extractTerm pi params[1]!
          pi := piloc
          pure (rightSubstMulti (parseListNat params[0]!) t (parseListString params[2]!))
        | "leftSubstMulti"           =>
          let (t, piloc) ← extractTerm pi params[1]!
          pi := piloc
          pure (leftSubstMulti (parseListNat params[0]!) t (parseListString params[2]!))
        | "rightSubstEqForallLocal"  =>
          let (t1, piloc) ← extractTerm pi params[1]!
          let (t2, piloc) ← extractTerm piloc params[1]!
          pi := piloc
          pure (rightSubstEqForallLocal (parseNat params[0]!) t1 t2)
        | "rightSubstEqForall"       =>
          let (t1, piloc) ← extractTerm pi params[1]!
          let (t2, piloc) ← extractTerm piloc params[1]!
          pi := piloc
          pure (rightSubstEqForall (parseNat params[0]!) t1 t2)
        | "rightSubstIffForallLocal" =>
          let (t1, piloc) ← extractTerm pi params[1]!
          let (t2, piloc) ← extractTerm piloc params[1]!
          pi := piloc
          pure (rightSubstIffForallLocal (parseNat params[0]!) t1 t2)
        | "rightSubstIffForall"      =>
          let (t1, piloc) ← extractTerm pi params[1]!
          let (t2, piloc) ← extractTerm piloc params[1]!
          pi := piloc
          pure (rightSubstIffForall (parseNat params[0]!) t1 t2)
        | "rightNnf"                 => pure (rightNnf (parseNat params[0]!) (parseNat params[1]!))
        | "rightPrenex"              => pure (rightPrenex (parseNat params[0]!) (parseNat params[1]!))
        | "clausify"                 => pure (clausify (parseNat params[0]!))
        | "elimIffRefl"              => pure (elimIffRefl (parseNat (params[0]!)))
        | "res"                      => pure (res (parseNat params[0]!))
        | "instMult"                 => panic! "instMult not implemented"

        | _ => panic! s!"parseInferenceRecord: unknown rule '{ruleName}'"
      return (⟨rule, premises⟩, pi)
  | _ => throwError "parseInferenceRecord: term is not an inference record"


structure ProofStep where
  name               : String
  rule               : InferenceRule
  premises           : List String
  antecedents        : List Expr
  consequents        : List Expr
deriving Inhabited, Repr

instance : Lean.ToMessageData ProofStep where
  toMessageData ps :=
    let nameField := m!"Name: " ++ ps.name
    let ruleField     := m!"Rule: {ps.rule}"
    let premisesField := m!"Premises: " ++
      (Lean.MessageData.sbracket <| Lean.MessageData.joinSep (ps.premises.map Lean.toMessageData) (Lean.Format.line))

    let antField := m!"Antecedents: " ++
      (Lean.MessageData.sbracket <| Lean.MessageData.joinSep (ps.antecedents.map Lean.toMessageData) (", " ++ Lean.Format.line))

    let conField := m!"Consequents: " ++
      (Lean.MessageData.sbracket <| Lean.MessageData.joinSep (ps.consequents.map Lean.toMessageData) (", " ++ Lean.Format.line))

    Lean.MessageData.group <|
      nameField ++ Lean.Format.align true ++
      ruleField ++ Lean.Format.align true ++
      premisesField ++ Lean.Format.align true ++
      antField ++ Lean.Format.align true ++
      conField

open Embedding.Lam in
/--
  Turn SC-TPTP proof into reified ProofSteps
-/
def getSCTPTPProof (cmds : Array Command) : LamReif.ReifM (Array ProofStep) := do
  let lamVarTy := (← LamReif.getVarVal).map Prod.snd
  let lamEVarTy ← LamReif.getLamEVarTy
  let mut pi : ParsingInfo := ⟨lamVarTy, lamEVarTy, {}, {}⟩
  let mut ret := #[]
  trace[auto.tptp.printProof] "###########################################"
  for ⟨cmd, args⟩ in cmds.reverse do
    match cmd with
    | "fof" =>
      trace[auto.tptp.printProof] "{decl_name%}: {cmd} {args}"
      match args with
      | ⟨.ident name, []⟩ :: ⟨.ident formulaKind, _⟩ :: sequent :: tail =>
        -- ### Reifing the inference record
        let infRec ← match formulaKind with
          | "axiom" => pure ⟨.hyp 0, []⟩
          | "plain" => match tail with
            | inferTerm :: [] =>
              let (infRec, piloc) ← parseInferenceRecord inferTerm pi
              pi := piloc
              pure infRec
            | _ => throwError "Unexpected formula kind: {formulaKind}"
          | _ => continue

        -- ### Reifing the sequent
        let (antecedents, consequents) ← match sequent with
          | ⟨.op "-->", antecedents :: consequents :: []⟩ =>
            let antecedents ← match antecedents with
            | ⟨.ident "list", antecedents⟩ =>
              let mut antExprs := #[]
              let mut piLoc := pi
              for ant in antecedents do
                let (expr, piNew) ← term2Expr piLoc ant
                antExprs := antExprs.push expr
                piLoc := piNew
                pi := piLoc
              pure antExprs.toList
            | _ => throwError "Expected list of antecedents"
            let consequents ← match consequents with
            | ⟨.ident "list", consequents⟩ =>
              let mut conExprs := #[]
              let mut piLoc := pi
              for con in consequents do
                let (expr, piNew) ← term2Expr piLoc con
                conExprs := conExprs.push expr
                piLoc := piNew
                pi := piLoc
              pure conExprs.toList
            | _ => throwError "Expected list of consequents"
            pure (antecedents, consequents)
          | consequent =>
            let (expr, piNew) ← term2Expr pi consequent
            pi := piNew
            pure ([], [expr])

        -- ### Instantiating the proof step
        let step: ProofStep := ⟨name, infRec.rule, infRec.premises, antecedents, consequents⟩
        ret := ret.push step

        trace[auto.tptp.printProof] m!"Reconstructed proof step:\n{step}"
        trace[auto.tptp.printProof] m!"New variables introduced so far: {pi.proverSkolem.toList.map (fun (x, _) => m!"{x}")}"

      | _ => continue
    | _ => throwError "{decl_name%} :: Unknown command {cmd}"
  return ret.reverse


#eval parse "fof(a0, axiom, (! [X0] : (X0 = app(t_a0, app(t_a0, app(t_a0, X0))))))."
#eval parse "fof(a0, axiom, (! [X0] : (X0 = app(t_a0, app(t_a0, app(t_a0, X0)))))).
fof(a1, axiom, (! [X0] : (! [X1] : (X0 = app(t_a0, app(t_a0, X0)))))).
fof(c, conjecture, (t_a1 = app(t_a0, t_a1)))."

#eval parse "fof(f1, plain, [q(b)] --> [], inference(instFun, [status(thm), 'X', $fot(b), []], [a1]))."

#eval parse "fof(f8, plain, [~((? [X05] : ((app(t_a0, X05) => (! [X17] : (app(t_a0, X17))))))), ~((app(t_a0, X05_9) => (! [X17] : (app(t_a0, X17))))), app(t_a0, X05_9), ~((! [X17] : (app(t_a0, X17)))), ~(app(t_a0, Sko_0)), ~((app(t_a0, Sko_0) => (! [X17] : (app(t_a0, X17))))), app(t_a0, Sko_0)] --> [], inference(leftHyp, [status(thm), 4], []))."

#eval parse "fof(-8, plain, [~((? [X05] : ((app(t_a0, X05) => (! [X17] : (app(t_a0, X17))))))), ~((app(t_a0, X05_9) => (! [X17] : (app(t_a0, X17))))), app(t_a0, X05_9), ~((! [X17] : (app(t_a0, X17)))), ~(app(t_a0, Sko_0)), ~((app(t_a0, Sko_0) => (! [X17] : (app(t_a0, X17))))), app(t_a0, Sko_0)] --> [], inference(leftHyp, [status(thm), 4], []))."

end TPTP
