import Auto.Tactic

-- set_option auto.smt true
-- set_option auto.smt.trust true
-- set_option trace.auto.smt.printCommands true
-- set_option trace.auto.smt.result true

set_option auto.tptp true
set_option auto.tptp.trust true
set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.result true

set_option auto.tptp.solver.name "egg"
-- set_option auto.tptp.egg.path "../egg-sc-tptp"
set_option auto.tptp.egg.path "/home/poiroux/Documents/EPFL/PhD/Lean/lean-auto/egg-sc-tptp"

set_option auto.mono.mode "fol"

set_option trace.auto.printLemmas true

-- example : True := by auto

-- example (p : Prop) : p -> p := by auto

-- example : ∀ (p : Prop), p -> p := by auto

-- example (p : Prop) : p ∨ ¬ p := by auto

-- fof(a1, axiom, (! [Xx]: ((Xx = sf(sf(sf(Xx))))))).
-- fof(a2, axiom, (! [Xx]: ((! [Xy]: ((Xx = sf(sf(Xx)))))))).
-- fof(c3, conjecture, (cemptySet = sf(cemptySet))).
theorem saturation (sf : Type -> Type) (cemptySet : Type)
  (h1 : ∀ x, x = sf (sf (sf x)))
  (h2 : ∀ x, (∀ y : Type, x = sf (sf x))) :
  cemptySet = sf cemptySet := by
  egg

-- fof(a1, axiom, (! [Xx]: ((p(Xx) <=> p(sf(sf(sf(sf(sf(sf(sf(sf(Xx))))))))))))).
-- fof(a2, axiom, (! [Xx]: ((p(Xx) <=> p(sf(sf(sf(sf(sf(Xx)))))))))).
-- fof(c3, conjecture, (p(sf(cemptySet)) <=> p(cemptySet))).
theorem testiff (p : Type -> Prop) (sf : Type -> Type) (cemptySet : Type)
  (h1 : ∀ x, p x ↔ p (sf (sf (sf (sf (sf (sf (sf (sf x)))))))))
  (h2 : ∀ x, p x ↔ p (sf (sf (sf (sf (sf x)))))) :
  p (sf cemptySet) ↔ p cemptySet := by
  egg

-- fof(c1, conjecture, ($true => (? [Xx]: ((sP(Xx) => (! [Xy]: (sP(Xy)))))))).
theorem buveurs (sP : Prop -> Prop) : ∃ x, (sP x) → (∀ y, sP y) := by
  egg
