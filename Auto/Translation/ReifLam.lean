import Auto.Translation.Lift
import Auto.Translation.LCtx
import Auto.Util.ExprExtra
import Auto.Util.SigEq
import Std.Data.List.Lemmas
import Mathlib.Data.Real.Basic
import Mathlib.Data.BitVec.Defs

-- Embedding Simply Typed Lambda Calculus into Dependent Type Theory
-- Simply Typed Lambda Calculus = HOL (without polymorphism)
namespace Auto.ReifLam
open Translation

-- Interpreted sorts
inductive LamBaseSort
  | prop : LamBaseSort             -- GLift `prop`
  | nat  : LamBaseSort             -- GLift `nat`
  | real : LamBaseSort             -- GLift `real`
  | bv   : (n : Nat) → LamBaseSort -- GLift `bv n`
deriving BEq, Hashable, Inhabited

def LamBaseSort.reprPrec (b : LamBaseSort) (n : Nat) :=
  let str :=
    match b with
    | .prop => ".prop"
    | .nat  => ".nat"
    | .real => ".real"
    | .bv n => s!".bv {n}"
  if n == 0 then
    f!"LamBaseSort." ++ str
  else
    f!"({str})"

instance : Repr LamBaseSort where
  reprPrec s n := s.reprPrec n

def LamBaseSort.beq : LamBaseSort → LamBaseSort → Bool
| .prop, .prop => true
| .nat,  .nat  => true
| .real, .real => true
| .bv n, .bv m => n == m
| _,     _     => false

def LamBaseSort.beq_refl : (b : LamBaseSort) → (b.beq b) = true
| .prop => rfl
| .nat  => rfl
| .real => rfl
| .bv n => Nat.beq_refl n

def LamBaseSort.beq_eq (b₁ b₂ : LamBaseSort) : b₁.beq b₂ → b₁ = b₂ :=
  match b₁, b₂ with
  | .prop, .prop => fun _ => rfl
  | .nat,  .nat  => fun _ => rfl
  | .real, .real => fun _ => rfl
  | .bv n, .bv m => fun H => Nat.eq_of_beq_eq_true H ▸ rfl
  | .prop, .nat  => fun H => by cases H
  | .prop, .real => fun H => by cases H
  | .prop, .bv m => fun H => by cases H
  | .nat,  .prop => fun H => by cases H
  | .nat,  .real => fun H => by cases H
  | .nat,  .bv m => fun H => by cases H
  | .real, .prop => fun H => by cases H
  | .real, .nat  => fun H => by cases H
  | .real, .bv m => fun H => by cases H
  | .bv n, .prop => fun H => by cases H
  | .bv n, .nat  => fun H => by cases H
  | .bv n, .real => fun H => by cases H

@[reducible] def LamBaseSort.interp.{u} : LamBaseSort → Type u
| .prop   => GLift Prop
| .nat    => GLift Nat
| .real   => GLift Real
| .bv n   => GLift (Bitvec n)

inductive LamSort
| atom : Nat → LamSort
| base : LamBaseSort → LamSort
| func : LamSort → LamSort → LamSort
deriving Inhabited, Hashable

def LamSort.reprPrec (s : LamSort) (n : Nat) :=
  let str :=
    match s with
    | .atom n     => f!".atom {n}"
    | .base b     => f!".base {LamBaseSort.reprPrec b 1}"
    | .func s1 s2 => f!".func {LamSort.reprPrec s1 1} {LamSort.reprPrec s2 1}"
  if n == 0 then
    f!"Auto.ReifLam.LamSort" ++ str
  else
    f!"({str})"

instance : Repr LamSort where
  reprPrec s n := s.reprPrec n 

def LamSort.beq : LamSort → LamSort → Bool
| .atom m,     .atom n     => m == n
| .base m,     .base n     => m.beq n
| .func m₁ n₁, .func m₂ n₂ => LamSort.beq m₁ m₂ && LamSort.beq n₁ n₂
| _,           _           => false

def LamSort.beq_refl : (a : LamSort) → (a.beq a) = true
| .atom m => Nat.beq_refl m
| .base b => LamBaseSort.beq_refl b
| .func m₁ n₁ => by rw [beq]; rw [LamSort.beq_refl m₁]; rw [LamSort.beq_refl n₁]; rfl

def LamSort.beq_eq (a b : LamSort) : (a.beq b = true) → a = b :=
  match a, b with
  | .atom m,     .atom n     => fun H => Nat.eq_of_beq_eq_true H ▸ rfl
  | .base m,     .base n     => fun H => LamBaseSort.beq_eq _ _ H ▸ rfl
  | .func m₁ n₁, .func m₂ n₂ => fun H => by
    simp [beq] at H; cases H;
    case intro left right =>
      let meq : m₁ = m₂ := LamSort.beq_eq m₁ m₂ left ▸ rfl
      let neq : n₁ = n₂ := LamSort.beq_eq n₁ n₂ right ▸ rfl
      rw [meq, neq]
  | .atom m,     .base n     => fun H => by cases H
  | .atom m,     .func m₁ n₁ => fun H => by cases H
  | .base m,     .atom n     => fun H => by cases H
  | .base m,     .func m₁ n₁ => fun H => by cases H
  | .func m₁ n₁, .atom n     => fun H => by cases H
  | .func m₁ n₁, .base n     => fun H => by cases H

theorem LamSort.beq_eq_true_eq (a b : LamSort) : (a.beq b = true) = (a = b) :=
  propext <| Iff.intro (beq_eq a b) (fun h => by subst h; apply beq_refl)

@[reducible] def LamSort.interp.{u} (val : Nat → Type u) : LamSort → Type u
| .atom n => val n
| .base b => b.interp
| .func dom cod => interp val dom → interp val cod

-- Representable real numbers
inductive CstrReal
  | zero    : CstrReal
  | one     : CstrReal
deriving Inhabited, Hashable

def CstrReal.reprPrec (c : CstrReal) (n : Nat) :=
  let s :=
    match c with
    | .zero => f!".zero"
    | .one  => f!".one"
  if n == 0 then
    f!"Auto.ReifLam.CstrReal." ++ s
  else
    f!"({s})"

instance : Repr CstrReal where
  reprPrec := CstrReal.reprPrec

def CstrReal.interp.{u} : (c : CstrReal) → GLift.{1, u} Real
| zero => GLift.up 0
| one  => GLift.up 1

inductive LamBaseTerm
  | trueE   : LamBaseTerm -- Propositional `true`
  | falseE  : LamBaseTerm -- Propositional `false`
  | not     : LamBaseTerm -- Propositional `not`
  | and     : LamBaseTerm -- Propositional `and`
  | or      : LamBaseTerm -- Propositional `or`
  | iff     : LamBaseTerm -- Propositional `iff`
  | natVal  : Nat → LamBaseTerm
  | realVal : CstrReal → LamBaseTerm
  | bvVal : List Bool → LamBaseTerm
  | eq      : LamSort → LamBaseTerm -- Polymorphic `eq`
  | forallE : LamSort → LamBaseTerm -- Polymorphic `forall`
  | existE : LamSort → LamBaseTerm -- Polymorphic `exists`
deriving Inhabited, Hashable

def LamBaseTerm.reprPrec (l : LamBaseTerm) (n : Nat) :=
  let s :=
    match l with
    | .trueE      => f!".trueE"
    | .falseE     => f!".falseE"
    | .not        => f!".not"
    | .and        => f!".and"
    | .or         => f!".or"
    | .iff        => f!".iff"
    | .natVal n   => f!".natVal {n}"
    | .realVal cr => f!".realVal {CstrReal.reprPrec cr 1}"
    | .bvVal l    => f!".bvVal {l}"
    | .eq s       => f!".eq {LamSort.reprPrec s 1}"
    | .forallE s  => f!".forallE {LamSort.reprPrec s 1}"
    | .existE s   => f!".existE {LamSort.reprPrec s 1}"
  if n == 0 then
    f!"Auto.ReifLam.LamBaseTerm." ++ s
  else
    f!"({s})"

instance : Repr LamBaseTerm where
  reprPrec := LamBaseTerm.reprPrec

def LamBaseTerm.check : LamBaseTerm → LamSort
| .trueE      => .base .prop
| .falseE     => .base .prop
| .not        => .func (.base .prop) (.base .prop)
| .and        => .func (.base .prop) (.func (.base .prop) (.base .prop))
| .or         => .func (.base .prop) (.func (.base .prop) (.base .prop))
| .iff        => .func (.base .prop) (.func (.base .prop) (.base .prop))
| .natVal n   => .base .nat
| .realVal cr => .base .real
| .bvVal ls   => .base (.bv ls.length)
| .eq s       => .func s (.func s (.base .prop))
| .forallE s  => .func (.func s (.base .prop)) (.base .prop)
| .existE s   => .func (.func s (.base .prop)) (.base .prop)

inductive LamBaseTerm.LamWF : LamBaseTerm → LamSort → Type
  | ofTrueE      : LamWF .trueE (.base .prop)
  | ofFalseE     : LamWF .falseE (.base .prop)
  | ofNot        : LamWF .not (.func (.base .prop) (.base .prop))
  | ofAnd        : LamWF .and (.func (.base .prop) (.func (.base .prop) (.base .prop)))
  | ofOr         : LamWF .or (.func (.base .prop) (.func (.base .prop) (.base .prop)))
  | ofIff        : LamWF .iff (.func (.base .prop) (.func (.base .prop) (.base .prop)))
  | ofNatVal n   : LamWF (.natVal n) (.base .nat)
  | ofRealVal cr : LamWF (.realVal cr) (.base .real)
  | ofBvVal ls   : LamWF (.bvVal ls) (.base (.bv ls.length))
  | ofEq s       : LamWF (.eq s) (.func s (.func s (.base .prop)))
  | ofForallE s  : LamWF (.forallE s) (.func (.func s (.base .prop)) (.base .prop))
  | ofExistE s   : LamWF (.existE s) (.func (.func s (.base .prop)) (.base .prop))

def LamBaseTerm.LamWF.reprPrec (wf : LamBaseTerm.LamWF s t) (n : Nat) :=
  let s :=
    match wf with
    | .ofTrueE      => f!".ofTrueE"
    | .ofFalseE     => f!".ofFalseE"
    | .ofNot        => f!".ofNot"
    | .ofAnd        => f!".ofAnd"
    | .ofOr         => f!".ofOr"
    | .ofIff        => f!".ofIff"
    | .ofNatVal n   => f!".ofNatVal {n}"
    | .ofRealVal cr => f!".ofRealVal {CstrReal.reprPrec cr 1}"
    | .ofBvVal ls   => f!".ofBvVal {ls}"
    | .ofEq s       => f!".ofEq {LamSort.reprPrec s 1}"
    | .ofForallE s  => f!".ofForallE {LamSort.reprPrec s 1}"
    | .ofExistE s   => f!".ofExistE {LamSort.reprPrec s 1}"
  if n == 0 then
    f!"Auto.ReifLam.LamBaseTerm.LamWF." ++ s
  else
    f!"({s})"

def LamBaseTerm.LamWF.ofLamBaseTerm : (b : LamBaseTerm) → (s : LamSort) × LamBaseTerm.LamWF b s
| .trueE      => ⟨.base .prop, .ofTrueE⟩
| .falseE     => ⟨.base .prop, .ofFalseE⟩
| .not        => ⟨.func (.base .prop) (.base .prop), .ofNot⟩
| .and        => ⟨.func (.base .prop) (.func (.base .prop) (.base .prop)), .ofAnd⟩
| .or         => ⟨.func (.base .prop) (.func (.base .prop) (.base .prop)), .ofOr⟩
| .iff        => ⟨.func (.base .prop) (.func (.base .prop) (.base .prop)), .ofIff⟩
| .natVal n   => ⟨.base .nat, .ofNatVal n⟩
| .realVal cr => ⟨.base .real, .ofRealVal cr⟩
| .bvVal ls   => ⟨.base (.bv ls.length), .ofBvVal ls⟩
| .eq s       => ⟨.func s (.func s (.base .prop)), .ofEq s⟩
| .forallE s  => ⟨.func (.func s (.base .prop)) (.base .prop), .ofForallE s⟩
| .existE s   => ⟨.func (.func s (.base .prop)) (.base .prop), .ofExistE s⟩

def LamBaseTerm.wf_complete (wf : LamBaseTerm.LamWF b s) : LamBaseTerm.LamWF.ofLamBaseTerm b = ⟨s, wf⟩ := by
  cases wf <;> rfl

def LamBaseTerm.check_of_LamWF (H : LamBaseTerm.LamWF b s) : b.check = s := by
  cases H <;> rfl

def LamBaseTerm.wf_of_Check (H : b.check = s) : LamBaseTerm.LamWF b s := by
  cases H; cases b <;> constructor

def LamBaseTerm.interp (tyVal : Nat → Type u) : (lwf : LamBaseTerm.LamWF b s) → s.interp tyVal
| .ofTrueE      => GLift.up true
| .ofFalseE     => GLift.up false
| .ofNot        => NotLift
| .ofAnd        => AndLift
| .ofOr         => OrLift
| .ofIff        => IffLift
| .ofNatVal n   => GLift.up n
| .ofRealVal cr => cr.interp
| .ofBvVal ls   => GLift.up ⟨ls, rfl⟩
| .ofEq s       => @EqLift (s.interp tyVal)
| .ofForallE s  => @ForallLift (s.interp tyVal)
| .ofExistE s   => @ExistsLift (s.interp tyVal)

inductive LamTerm
  | atom    : Nat → LamTerm
  | base    : LamBaseTerm → LamTerm
  | bvar    : Nat → LamTerm
  | lam     : LamSort → LamTerm → LamTerm
  | app     : LamTerm → LamTerm → LamTerm
deriving Inhabited, Hashable

def LamTerm.reprPrec (t : LamTerm) (n : Nat) :=
  let s :=
    match t with
    | .atom m => f!".atom {m}"
    | .base b => f!".base {LamBaseTerm.reprPrec b 1}"
    | .bvar m => f!".bvar {m}"
    | .lam s t => f!".lam {LamSort.reprPrec s 1} {LamTerm.reprPrec t 1}"
    | .app t₁ t₂ => f!".app {LamTerm.reprPrec t₁ 1} {LamTerm.reprPrec t₂ 1}"
  if n == 0 then
    f!"Auto.ReifLam.LamTerm" ++ s
  else
    f!"({s})"

instance : Repr LamTerm where
  reprPrec f n := LamTerm.reprPrec f n

-- Typecheck. `lamVarTy, lctx ⊢ term : type?`
-- `lamVarTy : Nat → LamSort` : Valuation
-- `Nat → LamSort`        : Local Context
def LamTerm.check (lamVarTy : Nat → LamSort) : (Nat → LamSort) → LamTerm → Option LamSort
| _,    .atom n  => lamVarTy n
| _,    .base b  => b.check
| lctx, .bvar n  => lctx n
| lctx, .lam s t =>
  match t.check lamVarTy (pushLCtx lctx s) with
  | .some ty => .some (.func s ty)
  | .none    => .none
| lctx, .app fn arg =>
  match fn.check lamVarTy lctx, arg.check lamVarTy lctx with
  | .some (.func ty₁ ty₂), .some argTy =>
    if ty₁.beq argTy then .some ty₂ else none
  | _, _ => .none

-- Judgement. `lamVarTy, lctx ⊢ term : type?`
structure LamJudge where
  lctx   : Nat → LamSort
  rterm  : LamTerm
  rty    : LamSort
deriving Inhabited

inductive LamWF (lamVarTy : Nat → LamSort) : LamJudge → Type
  | ofAtom
      {lctx : Nat → LamSort} (n : Nat) :
    LamWF lamVarTy ⟨lctx, .atom n, lamVarTy n⟩
  | ofBase
      {lctx : Nat → LamSort} {b : LamBaseTerm} {s : LamSort}
      (H : LamBaseTerm.LamWF b s) :
    LamWF lamVarTy ⟨lctx, .base b, s⟩
  | ofBVar
      {lctx : Nat → LamSort} (n : Nat) :
    LamWF lamVarTy ⟨lctx, .bvar n, lctx n⟩
  | ofLam
      {lctx : Nat → LamSort}
      {argTy : LamSort} (bodyTy : LamSort) {body : LamTerm}
      (H : LamWF lamVarTy ⟨pushLCtx lctx argTy, body, bodyTy⟩) :
    LamWF lamVarTy ⟨lctx, .lam argTy body, .func argTy bodyTy⟩
  | ofApp
      {lctx : Nat → LamSort}
      (argTy : LamSort) {resTy : LamSort}
      {fn : LamTerm} {arg : LamTerm}
      (HFn : LamWF lamVarTy ⟨lctx, fn, .func argTy resTy⟩)
      (HArg : LamWF lamVarTy ⟨lctx, arg, argTy⟩) :
    LamWF lamVarTy ⟨lctx, .app fn arg, resTy⟩

def LamWF.reprPrec (wf : LamWF f judge) (n : Nat) (lctxDep : Nat) :=
  let rec formatLCtxAux prec : (lctx : List LamSort) → Lean.Format
    | .nil => f!""
    | .cons a as => ", " ++ a.reprPrec prec ++ formatLCtxAux prec as
  let formatLCtx prec (lctx : Nat → LamSort) : (lctxDep : Nat) → Lean.Format
    | 0 => f!"[]"
    | n + 1 => f!"[" ++ (lctx 0).reprPrec prec ++
               formatLCtxAux prec ((List.range n).map (fun i => lctx (i + 1))) ++ f!"]"
  match wf with
  | @LamWF.ofAtom _ lctx m =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofAtom (lctx := {formatLCtx 1 lctx lctxDep}) {m}"
    else
      f!"(.ofAtom {m})"
  | @LamWF.ofBase _ lctx _ _ H =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofBase (lctx := {formatLCtx 1 lctx lctxDep}) {H.reprPrec 1}"
    else
      f!"(.ofBase {H.reprPrec 1})"
  | @LamWF.ofBVar _ lctx m =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofBVar (lctx := {formatLCtx 1 lctx lctxDep}) {m}"
    else
      f!"(.ofBVar {m})"
  | @LamWF.ofLam _ lctx argTy bodyTy body H =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofLam (lctx := {formatLCtx 1 lctx lctxDep}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (bodyTy := {bodyTy.reprPrec 1}) " ++
      f!"(body := {body.reprPrec 1}) {LamWF.reprPrec H 1 (lctxDep + 1)}"
    else
      f!"(.ofLam (argTy := {argTy.reprPrec 1}) (bodyTy := {bodyTy.reprPrec 1}) " ++
      f!"{LamWF.reprPrec H 1 (lctxDep + 1)})"
  | @LamWF.ofApp _ lctx argTy resTy fn arg HFn HArg =>
    if n == 0 then
      f!"Auto.ReifLam.LamWF.ofApp (lctx := {formatLCtx 1 lctx lctxDep}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (resTy := {resTy.reprPrec 1}) " ++
      f!"(fn := {fn.reprPrec 1}) (arg := {arg.reprPrec 1}) " ++
      f!"{LamWF.reprPrec HFn 1 lctxDep} {LamWF.reprPrec HArg 1 lctxDep}"
    else
      f!"(.ofApp (lctx := {formatLCtx 1 lctx lctxDep}) " ++
      f!"(argTy := {argTy.reprPrec 1}) (resTy := {resTy.reprPrec 1}) " ++
      f!"{LamWF.reprPrec HFn 1 lctxDep} {LamWF.reprPrec HArg 1 lctxDep})"

instance : Repr (LamWF lamVarTy judge) where
  reprPrec wf _ := LamWF.reprPrec wf 0 0

def LamWF.ofLamTerm {lamVarTy : Nat → LamSort} :
  {lctx : Nat → LamSort} → (t : LamTerm) → Option ((rty : LamSort) × LamWF lamVarTy ⟨lctx, t, rty⟩)
| lctx, .atom n => .some ⟨lamVarTy n, .ofAtom n⟩
| lctx, .base b =>
  let bWF := LamBaseTerm.LamWF.ofLamBaseTerm b
  .some ⟨bWF.fst, .ofBase bWF.snd⟩
| lctx, .bvar n => .some ⟨lctx n, .ofBVar n⟩
| lctx, .lam argTy body =>
  let bodyWf := @LamWF.ofLamTerm lamVarTy (pushLCtx lctx argTy) body
  match bodyWf with
  | .some ⟨bodyTy, wf⟩ => .some ⟨.func argTy bodyTy, .ofLam bodyTy wf⟩
  | .none => .none
| lctx, .app fn arg =>
  let fnWf := @LamWF.ofLamTerm lamVarTy lctx fn
  let argWf := @LamWF.ofLamTerm lamVarTy lctx arg
  match fnWf, argWf with
  | .some (⟨.func ty₁ ty₂, fnWf⟩), .some ⟨argTy, argWf⟩ =>
    match heq : ty₁.beq argTy with
    | true =>
      have tyEq := LamSort.beq_eq _ _ heq
      have fnWf' := tyEq ▸ fnWf
      .some ⟨ty₂, .ofApp argTy fnWf' argWf⟩
    | false => .none
  | _, _ => .none

-- #eval (@LamWF.ofLamTerm
--   (lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1))
--   (lctx := [])
--   (t := .lam (.atom 0) (.app (.atom 1) (.atom 0))))
-- 
-- #check Auto.ReifLam.LamWF.ofLam
--   (lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1))
--   (lctx := []) (argTy := (.atom 0)) (bodyTy := (.atom 1)) (body := (.app (.atom 1) (.atom 0))) (.ofApp (lctx := [(.atom 0)]) (argTy := (.atom 2)) (resTy := (.atom 1)) (.ofAtom 1) (.ofAtom 0))

def LamWF.complete_Aux
  {b : β} (p : Bool) (f : (p = true) → β) (eq : p = true) :
  (match (generalizing:=false) h : p with
  | true => f h
  | false => b) = f eq := by
  cases p
  case false => cases eq
  case true => simp

-- Of course `ofLamTerm` is sound with respect to `LamWF`. So, we
--   only need to show that it's complete
def LamWF.complete {lamVarTy : Nat → LamSort} :
  {j : LamJudge} → (wf : LamWF lamVarTy j) → LamWF.ofLamTerm j.rterm = .some ⟨j.rty, wf⟩
| .(_), @LamWF.ofAtom _ lctx n => rfl
| .(_), @LamWF.ofBase _ lctx b s h => by
  unfold ofLamTerm; rw [LamBaseTerm.wf_complete]
| .(_), @LamWF.ofBVar _ lctx n => rfl
| .(_), @LamWF.ofLam _ lctx argTy bodyTy body H => by
  unfold ofLamTerm;
  have IH := LamWF.complete H; simp at IH; rw [IH];
| .(_), @LamWF.ofApp _ lctx argTy resTy fn arg HFn HArg => by
  unfold ofLamTerm;
  have IHFn := LamWF.complete HFn
  have IHArg := LamWF.complete HArg
  simp at IHFn; simp at IHArg
  rw [IHFn]; rw [IHArg]; simp; rw [LamSort.beq_refl]

def LamTerm.check_of_lamWF
  {lamVarTy : Nat → LamSort} {lctx : Nat → LamSort} {t : LamTerm} {ty : LamSort} :
  LamWF lamVarTy ⟨lctx, t, ty⟩ → t.check lamVarTy lctx = .some ty := by
  generalize JudgeEq : { lctx := lctx, rterm := t, rty := ty : LamJudge} = Judge 
  intro HWf; revert lctx t ty JudgeEq; induction HWf
  case ofAtom lctx' n =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [rterm_eq, rty_eq]; rfl
  case ofBase lctx' b s H =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [rterm_eq, rty_eq]; sorry
  case ofBVar lctx' n =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq]; rfl
  case ofLam lctx' argTy bodyTy body H H_ih =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq];
    simp [check]; rw [H_ih]; rfl
  case ofApp lctx' argTy resTy fn arg HFn HArg HFn_ih HArg_ih =>
    intros lctx t ty JudgeEq
    injection JudgeEq with lctx_eq rterm_eq rty_eq;
    rw [lctx_eq, rterm_eq, rty_eq]
    simp [check];
    rw [@HFn_ih lctx' fn (LamSort.func argTy resTy)] <;> try rfl;
    rw [@HArg_ih lctx' arg argTy] <;> try rfl;
    simp [LamSort.beq_refl]

private def List.get?_eq_some' : {l : List α} → {n : Nat} → l.get? n = some a →
  (@PSigma (n < List.length l) (fun h => List.get l ⟨n, h⟩ = a))
| a::_,  0    , eq => ⟨Nat.succ_le_succ (Nat.zero_le _), by simp at eq; exact eq⟩
| _::as, n + 1, eq => by
    simp at eq; simp;
    match @List.get?_eq_some' α a as n eq with
    | PSigma.mk h' proof' =>
      apply PSigma.mk;
      case fst => apply Nat.succ_lt_succ; exact h'
      case snd => exact proof'
| .nil, _     , eq => by simp at eq

-- This function is meant to be `execute`-d (`eval`-ed), not `reduce`-d
-- **TODO**: Change type to `match` so that we don't need `rw`.
--   But do not delete this, because it shows problems (proof not fully reducing)
def LamTerm.lamWF_of_check {lamVarTy : Nat → LamSort} :
  {lctx : Nat → LamSort} → {t : LamTerm} → {ty : LamSort} →
  t.check lamVarTy lctx = .some ty → LamWF lamVarTy ⟨lctx, t, ty⟩
| lctx, .atom n, ty, HCheck => by
  simp [check] at HCheck; rw [← HCheck]; apply LamWF.ofAtom
| lctx, .base b, ty, HCheck => by
  simp [check] at HCheck; exact LamWF.ofBase (LamBaseTerm.wf_of_Check HCheck)
| lctx, .bvar n, ty, HCheck => by
  simp [check] at HCheck; rw [← HCheck]; apply LamWF.ofBVar
| lctx, .lam argTy body, ty, HCheck => by
  simp [check] at HCheck; revert HCheck
  cases CheckEq : check lamVarTy (pushLCtx lctx argTy) body
  case none => intro contra; cases contra
  case some bodyTy =>
    simp; intro tyEq; rw [← tyEq]
    apply LamWF.ofLam; apply (LamTerm.lamWF_of_check CheckEq)
| lctx, .app fn arg, ty, HCheck => by
  simp [check] at HCheck; revert HCheck
  match CheckFnEq : check lamVarTy lctx fn, CheckArgEq : check lamVarTy lctx arg with
  | .some (LamSort.func ty₁ ty₂), .some argTy =>
    simp;
    cases heq : LamSort.beq ty₁ argTy
    case false => intro contra; cases contra
    case true =>
      simp; intro H; rw [← H]; apply LamWF.ofApp (argTy:=ty₁);
      case HFn => apply (LamTerm.lamWF_of_check CheckFnEq)
      case HArg =>
        have heq' : ty₁ = argTy := LamSort.beq_eq _ _ heq
        rw [heq']
        apply (LamTerm.lamWF_of_check CheckArgEq)
  | .some (LamSort.func _ _), .none => intro contra; cases contra
  | .some (LamSort.atom _), _ => intro contra; cases contra
  | .some (LamSort.base _), _ => intro contra; cases contra
  | .none, _ => intro contra; cases contra

--#eval @LamTerm.wf_of_check
--  (lamVarTy := fun n => if n == 0 then .atom 2 else .func (.atom 2) (.atom 1))
--  (lctx := [])
--  (t := .lam (.atom 0) (.app (.atom 1) (.atom 0)))
--  (ty := .func (.atom 0) (.atom 1))
--  rfl

structure LamValuation.{u} where
  lamVarTy  : Nat → LamSort
  tyVal     : Nat → Type u
  varVal    : ∀ (n : Nat), (lamVarTy n).interp tyVal

def LamTerm.interp.{u} (lval : LamValuation.{u}) :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) →
  (lwf : LamWF lval.lamVarTy ⟨lctxTy, t, rty⟩) → rty.interp lval.tyVal
| lctxTy, lctxTerm, @LamWF.ofAtom _ _ n => lval.varVal n
| lctxTy, lctxTerm, @LamWF.ofBase _ _ b s H => LamBaseTerm.interp lval.tyVal H
| lctxTy, lctxTerm, @LamWF.ofBVar _ _ n => lctxTerm n
| lctxTy, lctxTerm, @LamWF.ofLam _ _ argTy _ body H =>
  fun (x : argTy.interp lval.tyVal) =>
    LamTerm.interp lval (pushLCtx lctxTy argTy) (pushLCtxDep lctxTerm x) H
| lctxTy, lctxTerm, @LamWF.ofApp _ _ _ resTy _ _ HFn HArg =>
  let mfn := LamTerm.interp lval lctxTy lctxTerm HFn
  let marg := LamTerm.interp lval lctxTy lctxTerm HArg
  mfn marg

-- Valuation
structure Valuation.{u} where
  -- Valuation of free type variables to constants in COC
  tyVal  : Nat → Type u
  -- valuation of free variables to constants in COC
  varTy  : Nat → Type u
  varVal : ∀ (n : Nat), varTy n

@[reducible] def Valuation.ofLamValuation : LamValuation → Valuation :=
  fun ⟨lamVarTy, tyVal, varVal⟩ => ⟨tyVal, fun n => (lamVarTy n).interp tyVal, varVal⟩

-- Judgement, `lctx ⊢ rterm ≝ mterm : ty`
structure Judgement.{u} where
  -- Local context, list of CIC terms
  lctxTy   : Nat → Type u
  lctxTerm : ∀ (n : Nat), lctxTy n
  -- A term in simply typed lambda calculus
  rterm    : LamTerm
  -- Type of `mterm`
  ty       : Type u
  -- The CIC term that `rterm` translates into
  mterm    : ty

set_option genInjectivity false in
inductive WF.{u} (val : Valuation.{u}) : Judgement.{u} → Type (u + 1)
  | ofAtom
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n} (n : Nat) :
    WF val <|
      ⟨lctxTy, lctxTerm, (.atom n), val.varTy n, val.varVal n⟩
  | ofBVar
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n} (n : Nat) :
    WF val <|
      ⟨lctxTy, lctxTerm, .bvar n, lctxTy n, lctxTerm n⟩
  | ofLam
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n}
      {hs : LamSort} {ht : LamTerm}
      (α β : Type u) (fn : α → β)
      (H : ∀ (t : α), WF val ⟨pushLCtx lctxTy α,
        (fun n => match n with | 0 => t | n + 1 => lctxTerm n), ht, β, fn t⟩)
      :
    WF val <|
      ⟨lctxTy, lctxTerm, .lam hs ht, α → β, fn⟩
  | ofApp
      {lctxTy : Nat → Type u}
      {lctxTerm : ∀ n : Nat, lctxTy n}
      {hfn harg : LamTerm}
      (α β : Type u) (fn : α → β) (arg : α)
      (Hfn : WF val ⟨lctxTy, lctxTerm, hfn, α → β, fn⟩)
      (Harg : WF val ⟨lctxTy, lctxTerm, harg, α, arg⟩)
      :
    WF val <|
      ⟨lctxTy, lctxTerm, .app hfn harg, β, fn arg⟩

def LamTerm.wf_of_lamWF.{u} (lval : LamValuation.{u}) :
  (lctxTy : Nat → LamSort) → (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) →
  (lwf : LamWF lval.lamVarTy ⟨lctxTy, t, rty⟩) →
  WF (Valuation.ofLamValuation lval)
    ⟨fun n => (lctxTy n).interp lval.tyVal, lctxTerm, t, rty.interp lval.tyVal, LamTerm.interp lval lctxTy lctxTerm lwf⟩
| lctxTy', lctxTerm', @LamWF.ofAtom _ _ n => WF.ofAtom _
| lctxTy', lctxTerm', @LamWF.ofBase _ _ b s H => _
| lctxTy', lctxTerm', @LamWF.ofBVar _ _ n => WF.ofBVar _
| lctxTy', lctxTerm', @LamWF.ofLam _ _ argTy bodyTy body H => @WF.ofLam (Valuation.ofLamValuation lval)
    (fun n => (lctxTy' n).interp lval.tyVal) lctxTerm'
    argTy body (LamSort.interp lval.tyVal argTy) (LamSort.interp lval.tyVal bodyTy)
    (LamTerm.interp lval lctxTy' lctxTerm' (LamWF.ofLam bodyTy H))
    (fun t' =>
      let ty₁ := fun n => LamSort.interp lval.tyVal (pushLCtx lctxTy' argTy n)
      let ty₂ := pushLCtx (fun n => LamSort.interp lval.tyVal (lctxTy' n)) (LamSort.interp lval.tyVal argTy)
      have hTyEq : ty₁ = ty₂ := by apply funext; intro n; cases n <;> simp
      let term₁ : ∀ (n : Nat), ty₁ n := fun n => match n with | 0 => t' | Nat.succ n => lctxTerm' n
      let term₂ : ∀ (n : Nat), ty₂ n := fun n => match n with | 0 => t' | Nat.succ n => lctxTerm' n
      have hTermEq : SigmaEq (fun (α : Nat → Type _) => (∀ (n : Nat), α n)) term₁ term₂ :=
        SigmaEq.of_heq (fun (α : Nat → Type u) => (n : Nat) → α n) (HEq.funext _ _ fun u =>
            match u with
            | 0 => HEq.refl _
            | n + 1 => HEq.refl _) hTyEq
      let motive := fun {ty : Nat → Type u} (term : ∀ n, ty n) =>
        WF (Valuation.ofLamValuation lval)
          ⟨ty, term, body, LamSort.interp lval.tyVal bodyTy, interp lval lctxTy' lctxTerm' (LamWF.ofLam bodyTy H) t'⟩
      let hWF : motive (ty:=ty₁) term₁ := LamTerm.wf_of_lamWF lval _ _ H
      @SigmaEq.ndrec (Nat → Type _) (fun α => (n : Nat) → α n) ty₁ term₁ motive hWF ty₂ term₂ hTermEq)
| lctxTy', lctxTerm', @LamWF.ofApp _ _ argTy resTy fn arg Hfn Harg =>
  let WFfn := LamTerm.wf_of_lamWF _ _ _ Hfn
  let WFarg := LamTerm.wf_of_lamWF _ _ _ Harg
  WF.ofApp _ _ _ _ WFfn WFarg

section Example
  
  def Nat.succLift.{u} (x : GLift.{1, u} Nat) :=
    GLift.up (Nat.succ x.down)

  -- Original: fun (x : Nat) => Nat.succ x
  -- Lifting to: fun (x : GLift Nat) => Nat.succLift x
  def interpEx₁.{u} : Judgement.{u} :=
    ⟨fun _ => Sort u, fun _ => PUnit, .lam (.atom 0) (.app (.atom 0) (.bvar 0)),
     GLift.{1, u} Nat → GLift.{1, u} Nat, fun (x : GLift Nat) => Nat.succLift x⟩
  
  def valuation₁.{u} : Valuation.{u} :=
    ⟨fun _ => GLift Nat,
     fun _ => GLift.{1, u} Nat → GLift.{1, u} Nat,
     fun _ => Nat.succLift⟩

  def wf₁.{u} : WF valuation₁.{u} interpEx₁.{u} := by
    apply WF.ofLam
    intro t
    apply WF.ofApp
    case Hfn =>
      apply WF.ofAtom
    case Harg =>
      apply WF.ofBVar

  -- Original: Nat.add 2 3
  -- Lifting to: GLift.up (Nat.add 2 3)
  def Nat.addLift.{u} (x y : GLift.{1, u} Nat) :=
    GLift.up (Nat.add (GLift.down x) (GLift.down y))

  def interpEx₂.{u} : Judgement.{u} :=
    ⟨fun _ => Sort u, fun _ => PUnit, .app (.app (.atom 0) (.atom 1)) (.atom 2),
      GLift.{1, u} Nat, GLift.up (Nat.add 2 3)⟩

  def valuation₂.{u} : Valuation.{u} :=
    ⟨fun _ => GLift Nat,
     fun n => [GLift.{1, u} Nat → GLift.{1, u} Nat → GLift.{1, u} Nat,
               GLift.{1, u} Nat, GLift.{1, u} Nat].getD n (GLift.{1, u} Nat),
     fun n =>
       match n with
       | 0 => Nat.addLift
       | 1 => GLift.up 2
       | 2 => GLift.up 3
       | _ + 3 => GLift.up 0⟩
  
  def wf₂.{u} : WF valuation₂.{u} interpEx₂.{u} := by
    apply WF.ofApp (fn := Nat.addLift (GLift.up 2))
    case Hfn =>
      apply WF.ofApp <;> apply WF.ofAtom
    case Harg =>
      apply WF.ofAtom

  -- Original: @Eq Nat 2 3
  -- Lifting to: GLift.up (@Eq Nat 2 3)
  -- **Note**: Sometimes we might want to lift to universe `u + 1`
  --   to avoid universe level issues.
  def interpEx₃.{u} : Judgement.{u + 1} :=
    ⟨fun _ => Type u, fun _ => Sort u, .app (.app (.atom 0) (.atom 1)) (.atom 2), Type u, GLift (2 = 3)⟩
  
  def valuation₃.{u} : Valuation.{u + 1} :=
    ⟨fun _ => GLift Nat,
    fun n => [GLift.{1, u + 1} Nat → GLift.{1, u + 1} Nat → Type u,
              GLift.{1, u + 1} Nat,
              GLift.{1, u + 1} Nat].getD n (GLift.{1, u + 1} Nat),
    fun n =>
      match n with
      | 0 => @EqLift.{1, u + 1, u} Nat
      | 1 => GLift.up 2
      | 2 => GLift.up 3
      | _ + 3 => GLift.up 0⟩

  def wf₃.{u} : WF valuation₃.{u} interpEx₃.{u} := by
    apply WF.ofApp (fn := @EqLift.{1, u + 1, u} Nat (GLift.up 2))
    case Hfn =>
      apply WF.ofApp <;> apply WF.ofAtom
    case Harg => apply WF.ofAtom

end Example

-- Changing all `.bvar ?n` in `t` (where `?n >= idx`) to `.bvar (Nat.succ ?n)`
def LamTerm.bvarLiftIdx (idx : Nat) : LamTerm → LamTerm
| .atom n     => .atom n
| .bvar n     => .bvar (popLCtxAt id idx n)
| .lam s t    => .lam s (t.bvarLiftIdx (Nat.succ idx))
| .app fn arg => .app (fn.bvarLiftIdx idx) (arg.bvarLiftIdx idx)

def LamTerm.bvarLift : LamTerm → LamTerm := LamTerm.bvarLiftIdx 0

def LamTerm.bvarLifts (t : LamTerm) : (lvl : Nat) → LamTerm
| 0 => t
| lvl' + 1 => (t.bvarLifts lvl').bvarLift

def LamTerm.bvarLifts_cast₁ {lvl : Nat} {rterm : LamTerm} (f : LamTerm → Sort u)
  (H : f (LamTerm.bvarLifts (LamTerm.bvarLift rterm) lvl)) :
  f (LamTerm.bvarLifts rterm (Nat.succ lvl)) :=
  match lvl with
  | 0 => H
  | lvl' + 1 => LamTerm.bvarLifts_cast₁ (rterm:=rterm) (f := fun t => f (t.bvarLift)) H

def LamTerm.bvarLifts_cast₂ {lvl : Nat} {rterm : LamTerm} (f : LamTerm → Sort u)
  (H : f (LamTerm.bvarLifts rterm (Nat.succ lvl))) :
  f (LamTerm.bvarLifts (LamTerm.bvarLift rterm) lvl) :=
  match lvl with
  | 0 => H
  | lvl' + 1 => LamTerm.bvarLifts_cast₂ (rterm:=rterm) (f := fun t => f (t.bvarLift)) H

def LamWF.ofBVarLiftIdx {lamVarTy lctx} (idx : Nat) (rterm : LamTerm) :
  (HWF : LamWF lamVarTy ⟨popLCtxAt lctx idx, rterm, rTy⟩) →
  LamWF lamVarTy ⟨lctx, rterm.bvarLiftIdx idx, rTy⟩
| .ofAtom n => .ofAtom n
| .ofBVar n =>
  let H := @LamWF.ofBVar lamVarTy lctx (popLCtxAt id idx n)
  let castHg := fun i => LamWF lamVarTy ⟨lctx, LamTerm.bvar (popLCtxAt id idx n), i⟩
  popLCtxAt.comm_cast₁ id lctx castHg idx n H
| .ofLam (argTy:=argTy) (body:=body) bodyTy wfBody =>
  .ofLam (argTy:=argTy) bodyTy
    (body:=body.bvarLiftIdx (Nat.succ idx))
    (LamWF.ofBVarLiftIdx (lctx:=pushLCtx lctx argTy) (Nat.succ idx) _ wfBody)
| .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.ofBVarLiftIdx idx _ HFn
  let IHArg := LamWF.ofBVarLiftIdx idx _ HArg
  .ofApp argTy' IHFn IHArg

def LamWF.ofBVarLift {lamVarTy lctx} (rterm : LamTerm) 
  (HWF : LamWF lamVarTy ⟨popLCtx lctx, rterm, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm.bvarLift, rTy⟩ :=
  LamWF.ofBVarLiftIdx 0 rterm HWF

def LamWF.ofBVarLifts {lamVarTy lctx} (rterm : LamTerm) (lvl : Nat)
  (HWF : LamWF lamVarTy ⟨popLCtxs lctx lvl, rterm, rTy⟩) :
  LamWF lamVarTy ⟨lctx, rterm.bvarLifts lvl, rTy⟩ :=
  match lvl with
  | 0 => HWF
  | lvl' + 1 =>
    let HWF' := LamWF.ofBVarLift rterm HWF
    let IH := LamWF.ofBVarLifts (LamTerm.bvarLift rterm) lvl' HWF'
    let castIH := fun t => LamWF lamVarTy ⟨lctx, t, rTy⟩
    LamTerm.bvarLifts_cast₁ castIH IH

def LamWF.fromBVarLiftIdx {lamVarTy} (idx : Nat) : {rTy : LamSort} →
  (rterm : LamTerm) → (HWF : LamWF lamVarTy ⟨lctx, rterm.bvarLiftIdx idx, rTy⟩) →
  LamWF lamVarTy ⟨popLCtxAt lctx idx, rterm, rTy⟩
| _, .atom n, .ofAtom _ => .ofAtom n
| _, .bvar n, .ofBVar _ =>
  let H := @LamWF.ofBVar lamVarTy (popLCtxAt lctx idx) n
  let castHg := fun i => LamWF lamVarTy ⟨popLCtxAt lctx idx, LamTerm.bvar n, i⟩
  popLCtxAt.comm_cast₂ id lctx castHg idx n H
| _, .lam argTy body, .ofLam bodyTy wfBody =>
  .ofLam (argTy:=argTy) bodyTy
    (LamWF.fromBVarLiftIdx (lctx:=pushLCtx lctx argTy) (Nat.succ idx) _ wfBody)
| _, .app fn arg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.fromBVarLiftIdx idx _ HFn
  let IHArg := LamWF.fromBVarLiftIdx idx _ HArg
  .ofApp argTy' IHFn IHArg

def LamWF.fromBVarLift {lamVarTy} {rty : LamSort}
  (rterm : LamTerm) (HWF : LamWF lamVarTy ⟨lctx, rterm.bvarLift, rty⟩) :
  LamWF lamVarTy ⟨popLCtx lctx, rterm, rty⟩ :=
  LamWF.fromBVarLiftIdx 0 rterm HWF

def LamWF.fromBVarLifts {lamVarTy lctx} (rterm : LamTerm) (lvl : Nat)
  (HWF : LamWF lamVarTy ⟨lctx, rterm.bvarLifts lvl, argTy⟩) :
  LamWF lamVarTy ⟨popLCtxs lctx lvl, rterm, argTy⟩ :=
  match lvl with
  | 0 => HWF
  | lvl' + 1 =>
    let HWF' := LamWF.fromBVarLift (LamTerm.bvarLifts rterm lvl') HWF
    let IH := LamWF.fromBVarLifts _ _ HWF'
    let castIH := fun f =>
      LamWF lamVarTy ⟨f, rterm, argTy⟩
    popLCtx.succ_cast₁ _ castIH _ IH

-- **Note**: This is the `.bvar` case for the following `LamWF.subst`
-- The `LamWF` of the `ofBVar` we've just destructed is equivalent to
--   `argTy::(idx)→lctx ⊢ (.bvar n) : (argTy::(idx)→lctx)[n]`
-- The `wfArg` is equivalent to saying
--  `lctx[idx:] ⊢ arg : argTy`
-- Which can be turned into
--  `lctx ⊢ (bVarLifts arg idx) : (argTy::(idx)→lctx)[idx]`
-- What we want is
--   1. n < idx : `lctx ⊢ (.bvar n) : lctx[n]`
--   2. n = idx : `lctx ⊢ (bVarLifts arg idx) : argTy`
--   3. n = n' + 1 > idx : `lctx ⊢ (.bvar n') : lctx[n']`
-- It helps to think of `lctx ⊢ (.bvar n) : lctx[n]` as being bvar lifted
--   from `lctx ⊢ (.bvar 0) : lctx[0]`
-- The required type is
--   `lctx ⊢ substed : (argTy::(idx)→lctx)[n]`
-- The required definitional equalities are
--   1. n < idx          ::   lctx[n]  == (argTy::(idx)→lctx)[n]
--   2. n = idx          ::   argTy    == (argTy::(idx)→lctx)[n]
--   3. n = n' + 1 > idx ::   lctx[n'] == (argTy::(idx)→lctx)[n]
-- The term will be defined recursively. So we will have the following situation:
-- 1. n >= idx, requires
--    `lctx ⊢ substed : (argTy::(2)→lctx)[4]`     (idx, n, lctx) := (2, 4, pop 0)
--    given `LamWF.ofBVarLifts wfArg ::: lctx ⊢ (bVarLifts arg 2) : (argTy::(2)→lctx)[4]`
--  i.e.
--    `lctx ⊢ substed : (lctx[0]::lctx[1]::argTy::lctx[2:])[4]`  := (2, 4, pop 0)
--    given `_ ::: lctx ⊢ (bVarLifts arg 2) : (lctx[0]::lctx[1]::argTy::lctx[2:])[4]`
--  This can be bvar lifted from
--    `lctx[1:] ⊢ substed : (lctx[1]::argTy::lctx[2:])[3]`       := (1, 3, pop 1)
--    given `_ ::: lctx[1:] ⊢ (bVarLifts arg 1) : (lctx[1]::argTy::lctx[2:])[3]`
--  This can in turn be bvar lifted from
--    `lctx[2:] ⊢ substed : (argTy::lctx[2:])[2]`                := (0, `n` = 2, pop 2)
--    given `_ ::: lctx[2:] ⊢ arg : (argTy::lctx[2:])[2]`
--  At this point, we should do `cases` on `n`.
--    (1). If `n = 0`, we should use `substed := arg`
--    (2). if `n = n' + 1`, we should use `substed := (.bvar n')`
-- 2. n < idx, requires
--    `lctx ⊢ substed : (argTy::(4)→lctx)[2]`     (idx, n, lctx) := (4, 2, pop 0)
--  i.e                                                          := (4, 2, pop 0)
--    `lctx ⊢ substed : (lctx[0]::lctx[1]::lctx[2]::lctx[3]::argTy::lctx[4:])[2]`
--  This can be bvar lifted from                                 := (3, 1, pop 1)
--    `lctx[1:] ⊢ substed : (lctx[1]::lctx[2]::lctx[3]::argTy::lctx[4:])[1]`
--  This can in turn be bvar lifted from                         := (`idx'` = 2, 0, pop 2)
--    `lctx[2:] ⊢ substed : (lctx[2]::lctx[3]::argTy::lctx[4])[0]`
--  At this point, it's clear that `substed := (.bvar 0)`
-- **TODO**: Can this function be represented by `pushLCtxDep`?
--           Furthermore, can other functions be represented by `pushLCtxDep`?
private def LamWF.subst_bvarAux
  {lamVarTy lctx : Nat → LamSort} {argTy : LamSort}
  (arg : LamTerm) (pops : Nat) : (idx : Nat) → (n : Nat) →
  (wfArg : LamWF lamVarTy ⟨popLCtxs lctx pops, arg.bvarLifts idx, argTy⟩) → 
  (substed : LamTerm) × LamWF lamVarTy ⟨(popLCtxs lctx pops), substed, pushLCtxAt (popLCtxs lctx pops) argTy idx n⟩
  | 0 => fun n =>
    match n with
    | 0 => fun wfArg =>
      ⟨arg, wfArg⟩
    | n' + 1 => fun wfArg =>
      ⟨.bvar n', .ofBVar _⟩
  | idx' + 1 => fun n =>
    match n with
    | 0 => fun wfArg =>
      ⟨.bvar 0, .ofBVar _⟩
    | n' + 1 => fun wfArg =>
      let wfArg' : LamWF lamVarTy _ :=
        LamWF.fromBVarLift (lctx:=popLCtxs lctx pops) _ wfArg
      let IH := LamWF.subst_bvarAux arg (Nat.succ pops) idx' n' wfArg'
      ⟨IH.fst.bvarLift, LamWF.ofBVarLift _ IH.snd⟩

-- Suppose we have `(λ x. func[body]) arg`
--   and `body` is a subterm of `func` under `idx` levels of binders in `func`.
--   We want to compute what `body` will become when we beta-reduce the whole term
-- `bj` is the judgement related to the body, i.e. `lctx ⊢ body : ty`. It's
--   easy to see that the `lctx` which `arg` resides in is `popLCtxs lctx (idx + 1)`
--   and the type of `arg` is `lctx idx`
def LamWF.subst (lamVarTy : Nat → LamSort) (idx : Nat)
  (arg : LamTerm) (argTy : LamSort)
  (body : LamTerm) (bodyTy : LamSort) :
  (lctx : Nat → LamSort) → 
  (wfArg : LamWF lamVarTy ⟨lctx, LamTerm.bvarLifts arg idx, argTy⟩) →
  (wfBody : LamWF lamVarTy ⟨pushLCtxAt lctx argTy idx, body, bodyTy⟩) →
  (substed : LamTerm) × LamWF lamVarTy ⟨lctx, substed, bodyTy⟩
| lctx, _,     .ofAtom n => ⟨.atom n, .ofAtom _⟩
| lctx, wfArg, .ofBVar n => LamWF.subst_bvarAux arg 0 idx n wfArg
| lctx, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  let wfArg' := LamWF.ofBVarLift (lctx:=pushLCtx lctx argTy') _ wfArg
  let IHArg := LamWF.subst lamVarTy (Nat.succ idx) _ _ _ _ _ wfArg' H
  ⟨.lam argTy' IHArg.fst, .ofLam _ IHArg.snd⟩
| lctx, wfArg, .ofApp argTy' HFn HArg =>
  let IHFn := LamWF.subst lamVarTy idx _ _ _ _ _ wfArg HFn
  let IHArg := LamWF.subst lamVarTy idx _ _ _ _ _ wfArg HArg
  ⟨.app IHFn.fst IHArg.fst, .ofApp argTy' IHFn.snd IHArg.snd⟩

def LamWF.subst_correct.{u} (lval : LamValuation.{u})
  (arg : LamTerm) (argTy : LamSort)
  (body : LamTerm) (bodyTy : LamSort) (idx : Nat) :
  (lctxTy : Nat → LamSort) →
  (lctxTerm : ∀ n, (lctxTy n).interp lval.tyVal) →
  (wfArg : LamWF lval.lamVarTy ⟨lctxTy, LamTerm.bvarLifts arg idx, argTy⟩) →
  (wfBody : LamWF lval.lamVarTy ⟨pushLCtxAt lctxTy argTy idx, body, bodyTy⟩) →
  let wfSubst := LamWF.subst lval.lamVarTy idx arg argTy body bodyTy lctxTy wfArg wfBody
  (LamTerm.interp lval (pushLCtxAt lctxTy argTy idx)
    (pushLCtxAtDep lctxTerm (LamTerm.interp lval lctxTy lctxTerm wfArg) idx) wfBody
  = LamTerm.interp lval lctxTy lctxTerm wfSubst.snd)
| lctxTy, lctxTerm, wfArg, .ofAtom n => rfl
| lctxTy, lctxTerm, wfArg, .ofBVar n => by simp [subst, LamTerm.interp]; sorry
  -- This seems to be implying that
  -- 1. We should state a commutativity theorem about `pushLCtxAtDep`
  -- 1. `Auto.ReifLam.LamWF.subst_bvarAux` should be expressed by `pushLCtxAtDep`
| lctxTy, lctxTerm, wfArg, .ofLam (argTy:=argTy') bodyTy' (body:=body') H =>
  sorry
| lctxTy, lctxTerm, wfArg, .ofApp argTy' HFn HArg =>
  sorry

end Auto.ReifLam