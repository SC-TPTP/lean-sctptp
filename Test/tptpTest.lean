import Auto.Tactic

-- set_option auto.smt true
-- set_option auto.smt.trust true
-- set_option trace.auto.smt.printCommands true
-- set_option trace.auto.smt.result true

set_option auto.tptp true
set_option auto.tptp.trust true
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true

set_option auto.mono.mode "fol"

example : True := by auto

example (p : Prop) : p -> p := by auto

example : ∀ (p : Prop), p -> p := by auto

example (p : Prop) : p ∨ ¬ p := by auto

-- fof(c1, conjecture, ($true => (? [Xx]: ((sP(Xx) => (! [Xy]: (sP(Xy)))))))).
theorem buveurs (sP : Prop -> Prop) : ∃ x, (sP x) → (∀ y, sP y) := by
  auto

-- fof(a1, axiom, (! [Xx]: ((Xx = sf(sf(sf(Xx))))))).
-- fof(a2, axiom, (! [Xx]: ((! [Xy]: ((Xx = sf(sf(Xx)))))))).
-- fof(c3, conjecture, (cemptySet = sf(cemptySet))).
theorem saturation (sf : Type -> Type) (cemptySet : Type)
  (h1 : ∀ x, sf (sf (sf x)) = x)
  (h2 : ∀ x, sf (sf x) = x) :
  cemptySet = sf cemptySet := by
  auto
