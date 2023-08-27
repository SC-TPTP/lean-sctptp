import Lean
import Mathlib.Data.Set.Intervals.Basic
import Mathlib.FieldTheory.Fixed
import Mathlib.Algebra.Hom.Group

section InstExamples

  /-
    No subterm of the type of `@Bool.not_beq_false` depends on the
      binder `b`, so `b` does not have to be instantiated. 
  -/
  set_option pp.all true in
  #check @Bool.not_beq_false

  /-
    No subterm of the type of `@Set.mem_Icc` depends on the binder
      `a, b, x`, so `a, b, x` does not have to be instantiated

    On the other hand, the type of the bound variable `x` inside
      `x ∈ Set.Icc a b ↔ a ≤ x ∧ x ≤ b` depends on `α`, so `α`
      must be instantiated
  -/
  #check @Set.mem_Icc

  /-
    Subterm `[inst_2 : MulSemiringAction G F]` depends on both
      `F` and `G`, so both `F` and `G` must be instantiated

    In fact, all the dependent `∀` binders must be instantiated,
      since those apart from `F` and `G` are all `instImplicit`.
  -/
  #check @FixedPoints.linearIndependent_smul_of_linearIndependent

  #check @injective_iff_map_eq_zero

  #check HAdd.hAdd

end InstExamples