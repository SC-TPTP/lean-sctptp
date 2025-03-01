import Auto.Tactic

-- set_option auto.smt true
-- set_option auto.smt.trust true
-- set_option trace.auto.smt.printCommands true
-- set_option trace.auto.smt.result true

set_option auto.tptp true
set_option auto.tptp.trust true
set_option auto.tptp.solver.name "egg"
set_option auto.tptp.egg.path "/home/poiroux/Documents/EPFL/PhD/Lean/lean-auto/egg-sc-tptp"

set_option trace.auto.tptp.printQuery true
set_option trace.auto.tptp.printProof true
set_option trace.auto.tptp.result true
set_option trace.auto.tactic.printProof true
set_option trace.auto.lamReif.printValuation true

set_option auto.mono.mode "fol"

-- set_option trace.auto.printLemmas true


-- fof(c, conjecture, (t_a0 = t_a0)).
example : A = A := by
  egg

  -- fof(f0, plain, [] --> [(t_a0 = t_a0)], inference(rightRefl, [status(thm), 0], [])).
  rfl


example : a -> (a /\ (a \/ b)) := by
  -- fof(f4, plain, [] --> [a -> (a & (a | b))], inference(rightImplies, [status(thm), 0], [f3])
  intro Ha

  -- fof(f3, plain, [a] --> [a & (a | b)], inference(rightAnd, [status(thm), 0], [f0, f2])
  constructor

  -- fof(f0, plain, [a] --> [a] , inference(hyp, [status(thm), 0], [])
  exact Ha

  -- fof(f2, plain, [a] --> [(a | b)], inference(rightOr, [status(thm), 0], [f1])
  left

  -- fof(f1, plain, [a] --> [a], inference(hyp, [status(thm), 0], [])
  exact Ha


-- fof(a0, axiom, (! [X0] : (X0 = app(t_a0, app(t_a0, app(t_a0, X0)))))).
-- fof(a1, axiom, (! [X0] : (! [X1] : (X0 = app(t_a0, app(t_a0, X0)))))).
-- fof(c, conjecture, (t_a1 = app(t_a0, t_a1))).

-- fof(f0, plain, [] --> [(t_a1 = t_a1)], inference(rightRefl, [status(thm), 0], [])).
-- fof(f1, plain, [(t_a1 = app(t_a0, app(t_a0, app(t_a0, t_a1))))] --> [(t_a1 = app(t_a0, app(t_a0, app(t_a0, t_a1))))], inference(rightSubstEq, [status(thm), 0, $fof((t_a1 = HOLE)), 'HOLE'], [f0])).
-- fof(f2, plain, [![X0] : (X0 = app(t_a0, app(t_a0, app(t_a0, X0))))] --> [(t_a1 = app(t_a0, app(t_a0, app(t_a0, t_a1))))], inference(leftForall, [status(thm), 0, $fot(t_a1)], [f1])).
-- fof(f3, plain, [] --> [(t_a1 = app(t_a0, app(t_a0, app(t_a0, t_a1))))], inference(cut, [status(thm), 0, 0], [a0, f2])).
-- fof(f4, plain, [(app(t_a0, t_a1) = app(t_a0, app(t_a0, app(t_a0, t_a1))))] --> [(t_a1 = app(t_a0, t_a1))], inference(rightSubstEq, [status(thm), 0, $fof((t_a1 = HOLE)), 'HOLE'], [f3])).
-- fof(f5, plain, [![X1] : (app(t_a0, t_a1) = app(t_a0, app(t_a0, app(t_a0, t_a1))))] --> [(t_a1 = app(t_a0, t_a1))], inference(leftForall, [status(thm), 0, $fot(X1)], [f4])).
-- fof(f6, plain, [![X0, X1] : (X0 = app(t_a0, app(t_a0, X0)))] --> [(t_a1 = app(t_a0, t_a1))], inference(leftForall, [status(thm), 0, $fot(app(t_a0, t_a1))], [f5])).
-- fof(f7, plain, [] --> [(t_a1 = app(t_a0, t_a1))], inference(cut, [status(thm), 0, 0], [a1, f6])).
example (α : Type) (t_a0 : α -> α) (t_a1 : α)
  (h1 : ∀ x, x = t_a0 (t_a0 (t_a0 x)))
  (h2 : ∀ x, ∀ y : α, x = t_a0 (t_a0 x))
  : t_a1 = (t_a0 t_a1) := by
  egg
  -- fof(f7, plain, [] --> [(t_a1 = app(t_a0, t_a1))], inference(cut, [status(thm), 0, 0], [a1, f6])).
  have H : ∀ x0 x1 : α, x0 = t_a0 (t_a0 x0) := by
    exact h2 --a1

  -- fof(f6, plain, [![X0, X1] : (X0 = app(t_a0, app(t_a0, X0)))] --> [(t_a1 = app(t_a0, t_a1))], inference(leftForall, [status(thm), 0, $fot(app(t_a0, t_a1))], [f5])).
  specialize H (t_a0 t_a1)

  -- fof(f5, plain, [![X1] : (app(t_a0, t_a1) = app(t_a0, app(t_a0, app(t_a0, t_a1))))] --> [(t_a1 = app(t_a0, t_a1))], inference(leftForall, [status(thm), 0, $fot(X1)], [f4])).
  specialize H ‹_›

  -- fof(f4, plain, [(app(t_a0, t_a1) = app(t_a0, app(t_a0, app(t_a0, t_a1))))] --> [(t_a1 = app(t_a0, t_a1))], inference(rightSubstEq, [status(thm), 0, $fof((t_a1 = HOLE)), 'HOLE'], [f3])).
  first |
    apply Eq.subst H (motive := λ x => t_a1 = x) |
    apply Eq.subst H.symm (motive := λ x => t_a1 = x)

  -- fof(f3, plain, [] --> [(t_a1 = app(t_a0, app(t_a0, app(t_a0, t_a1))))], inference(cut, [status(thm), 0, 0], [a0, f2])).
  have H1 : ∀ x, x = t_a0 (t_a0 (t_a0 x)) := by
    exact h1 --a0

  -- fof(f2, plain, [![X0] : (X0 = app(t_a0, app(t_a0, app(t_a0, X0))))] --> [(t_a1 = app(t_a0, app(t_a0, app(t_a0, t_a1))))], inference(leftForall, [status(thm), 0, $fot(t_a1)], [f1])).
  specialize H1 (t_a1)

  -- fof(f1, plain, [(t_a1 = app(t_a0, app(t_a0, app(t_a0, t_a1))))] --> [(t_a1 = app(t_a0, app(t_a0, app(t_a0, t_a1))))], inference(rightSubstEq, [status(thm), 0, $fof((t_a1 = HOLE)), 'HOLE'], [f0])).
  first |
    apply Eq.subst H1 (motive := λ x => t_a1 = x) |
    apply Eq.subst H1.symm (motive := λ x => t_a1 = x)

  -- fof(f0, plain, [] --> [(t_a1 = t_a1)], inference(rightRefl, [status(thm), 0], [])).
  rfl



-- fof(a0, axiom, (! [X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0)))))))))))).
-- fof(a1, axiom, (! [X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0))))))))).
-- fof(c, conjecture, (app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, t_a2))).

-- fof(e0, plain, [app(t_a0, app(t_a1, t_a2))] --> [app(t_a0, app(t_a1, t_a2))], inference(hyp, [status(thm), 0], [])).
-- fof(e1, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) => app(t_a0, app(t_a1, t_a2)))], inference(rightImplies, [status(thm), 0], [e0])).
-- fof(f0, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, t_a2)))], inference(rightIff, [status(thm), 0], [e1, e1])).
-- fof(f1, plain, [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))], inference(rightSubstIff, [status(thm), 0, $fof((app(t_a0, app(t_a1, t_a2)) <=> HOLE)), 'HOLE'], [f0])).
-- fof(f2, plain, [![X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0)))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))], inference(leftForall, [status(thm), 0, $fot(app(t_a1, t_a2))], [f1])).
-- fof(f3, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))], inference(cut, [status(thm), 0, 0], [a1, f2])).
-- fof(f4, plain, [(app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))))))], inference(rightSubstIff, [status(thm), 0, $fof((app(t_a0, app(t_a1, t_a2)) <=> HOLE)), 'HOLE'], [f3])).
-- fof(f5, plain, [![X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0)))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))))))], inference(leftForall, [status(thm), 0, $fot(app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))], [f4])).
-- fof(f6, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))))))], inference(cut, [status(thm), 0, 0], [a1, f5])).
-- fof(f7, plain, [(app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))))) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))))))))], inference(rightSubstIff, [status(thm), 0, $fof((app(t_a0, app(t_a1, t_a2)) <=> HOLE)), 'HOLE'], [f6])).
-- fof(f8, plain, [![X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0)))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))))))))], inference(leftForall, [status(thm), 0, $fot(app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))], [f7])).
-- fof(f9, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))))))))], inference(cut, [status(thm), 0, 0], [a1, f8])).
-- fof(f10, plain, [(app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))], inference(rightSubstIff, [status(thm), 0, $fof((app(t_a0, app(t_a1, t_a2)) <=> HOLE)), 'HOLE'], [f9])).
-- fof(f11, plain, [![X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))], inference(leftForall, [status(thm), 0, $fot(app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))], [f10])).
-- fof(f12, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))], inference(cut, [status(thm), 0, 0], [a0, f11])).
-- fof(f13, plain, [(app(t_a0, t_a2) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, t_a2))], inference(rightSubstIff, [status(thm), 0, $fof((app(t_a0, app(t_a1, t_a2)) <=> HOLE)), 'HOLE'], [f12])).
-- fof(f14, plain, [![X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, t_a2))], inference(leftForall, [status(thm), 0, $fot(t_a2)], [f13])).
-- fof(f15, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, t_a2))], inference(cut, [status(thm), 0, 0], [a0, f14])).
theorem testiff (α : Type) (p : α -> Prop) (sf : α -> α) (cemptySet : α)
  (h1 : ∀ x, p x ↔ p (sf (sf (sf (sf (sf (sf (sf (sf x)))))))))
  (h2 : ∀ x, p x ↔ p (sf (sf (sf (sf (sf x)))))) :
  p (sf cemptySet) ↔ p cemptySet := by
  -- fof(f15, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, t_a2))], inference(cut, [status(thm), 0, 0], [a0, f14])).
  have H : ∀ x, p x ↔ p (sf (sf (sf (sf (sf (sf (sf (sf x)))))))) := by
    exact h1

  -- fof(f14, plain, [![X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, t_a2))], inference(leftForall, [status(thm), 0, $fot(t_a2)], [f13])).
  specialize H cemptySet

  -- fof(f13, plain, [(app(t_a0, t_a2) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, t_a2))], inference(rightSubstIff, [status(thm), 0, $fof((app(t_a0, app(t_a1, t_a2)) <=> HOLE)), 'HOLE'], [f12])).
  apply Iff.subst H.symm (p := λ x => p (sf cemptySet) ↔ x)

  -- fof(f12, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))], inference(cut, [status(thm), 0, 0], [a0, f11])).
  have H1 : ∀ x, p x ↔ p (sf (sf (sf (sf (sf (sf (sf (sf x)))))))) := by
    exact h1

  -- fof(f11, plain, [![X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))], inference(leftForall, [status(thm), 0, $fot(app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))], [f10])).
  specialize H1 (sf (sf (sf (sf (sf (sf (sf (sf cemptySet))))))))

  -- fof(f10, plain, [(app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))], inference(rightSubstIff, [status(thm), 0, $fof((app(t_a0, app(t_a1, t_a2)) <=> HOLE)), 'HOLE'], [f9])).
  apply Iff.subst H1.symm (p := λ x => p (sf cemptySet) ↔ x)

  -- fof(f9, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))))))))], inference(cut, [status(thm), 0, 0], [a1, f8])).
  have H2 : ∀ x, p x ↔ p (sf (sf (sf (sf (sf x))))) := by
    exact h2

  -- fof(f8, plain, [![X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0)))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))))))))], inference(leftForall, [status(thm), 0, $fot(app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))], [f7])).
  specialize H2 (sf (sf (sf (sf (sf (sf (sf (sf (sf (sf (sf cemptySet)))))))))))

  -- fof(f7, plain, [(app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))))) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))))))))))))], inference(rightSubstIff, [status(thm), 0, $fof((app(t_a0, app(t_a1, t_a2)) <=> HOLE)), 'HOLE'], [f6])).
  apply Iff.subst H2 (p := λ x => p (sf cemptySet) ↔ x)

  -- fof(f6, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))))))], inference(cut, [status(thm), 0, 0], [a1, f5])).
  have H3 : ∀ x, p x ↔ p (sf (sf (sf (sf (sf x))))) := by
    exact h2

  -- fof(f5, plain, [![X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0)))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))))))], inference(leftForall, [status(thm), 0, $fot(app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))], [f4])).
  specialize H3 (sf (sf (sf (sf (sf (sf cemptySet))))))

  -- fof(f4, plain, [(app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2)))))))))))))], inference(rightSubstIff, [status(thm), 0, $fof((app(t_a0, app(t_a1, t_a2)) <=> HOLE)), 'HOLE'], [f3])).
  apply Iff.subst H3 (p := λ x => p (sf cemptySet) ↔ x)

  -- fof(f3, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))], inference(cut, [status(thm), 0, 0], [a1, f2])).
  have H4 : ∀ x, p x ↔ p (sf (sf (sf (sf (sf x))))) := by
    exact h2

  -- fof(f2, plain, [![X0] : (app(t_a0, X0) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, X0)))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))], inference(leftForall, [status(thm), 0, $fot(app(t_a1, t_a2))], [f1])).
  specialize H4 (sf cemptySet)

  -- fof(f1, plain, [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, app(t_a1, t_a2))))))))], inference(rightSubstIff, [status(thm), 0, $fof((app(t_a0, app(t_a1, t_a2)) <=> HOLE)), 'HOLE'], [f0])).
  apply Iff.subst H4 (p := λ x => p (sf cemptySet) ↔ x)

  -- fof(f0, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) <=> app(t_a0, app(t_a1, t_a2)))], inference(rightIff, [status(thm), 0], [e1, e1])).
  constructor

  -- fof(e1, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) => app(t_a0, app(t_a1, t_a2)))], inference(rightImplies, [status(thm), 0], [e0])).
  intro e1

  -- fof(e0, plain, [app(t_a0, app(t_a1, t_a2))] --> [app(t_a0, app(t_a1, t_a2))], inference(hyp, [status(thm), 0], [])).
  assumption

  -- fof(e1, plain, [] --> [(app(t_a0, app(t_a1, t_a2)) => app(t_a0, app(t_a1, t_a2)))], inference(rightImplies, [status(thm), 0], [e0])).
  intro e1

  -- fof(e0, plain, [app(t_a0, app(t_a1, t_a2))] --> [app(t_a0, app(t_a1, t_a2))], inference(hyp, [status(thm), 0], [])).
  assumption

-- fof(c1, conjecture, ($true => (? [Xx]: ((sP(Xx) => (! [Xy]: (sP(Xy)))))))).
theorem buveurs (sP : Prop -> Prop) : ∃ x, (sP x) → (∀ y, sP y) := by
  egg
