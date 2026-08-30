/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import OSforGFF.Measure.IsGaussian
import OSforGFF.Spacetime.Euclidean
import OSforGFF.Measure.GaussianFreeField

/-!
# OS2 — Euclidean Invariance

Proves Z[Ef] = Z[f] for any Euclidean transformation E ∈ E(d) (rotation/reflection
plus translation). The argument:

1. Change variables x → E⁻¹x, y → E⁻¹y in the covariance integral
2. C(x,y) = Cprofile |x−y| depends only on |x−y|, so C(E⁻¹x, E⁻¹y) = C(x,y)
3. Lebesgue measure on ℝ^d is invariant: dᵈ(E⁻¹x) = dᵈx (since |det R| = 1)

Hence S(Ef) = ∫∫ f*(x) C(x,y) f(y) dx dy = S(f).

## Main results

- `freeCovarianceℂ_bilinear_euclidean_invariant`
- `CovarianceEuclideanInvariantℂ_μ_GFF`
-/

open MeasureTheory Complex Real Filter OSforGFF
open scoped Real BigOperators

noncomputable section

namespace QFT

variable {d : ℕ} [Fact (2 ≤ d)] (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]

/-! ## Euclidean action on test functions -/

omit [Fact (2 ≤ d)] in
/-- The Euclidean action satisfies (g • f)(x) = f(g⁻¹ • x). -/
lemma euclidean_action_apply (g : E d) (f : SchwartzTestFunctionℂ d) (x : SpaceTime d) :
    euclidean_action g f x = f (euclidean_pullback g x) := by
  unfold euclidean_action
  simp only [SchwartzMap.compCLM_apply]
  rfl

omit [Fact (2 ≤ d)] in
/-- The Euclidean pullback satisfies euclidean_pullback g x = g⁻¹ • x = act g⁻¹ x. -/
lemma euclidean_pullback_eq_inv_act (g : E d) (x : SpaceTime d) :
    euclidean_pullback g x = act g⁻¹ x := rfl

omit [Fact (2 ≤ d)] in
/-- Composing pullbacks: euclidean_pullback g (act g y) = y. -/
lemma euclidean_pullback_act (g : E d) (y : SpaceTime d) :
    euclidean_pullback g (act g y) = y := by
  simp only [euclidean_pullback_eq_inv_act, act_inv_general]

omit [Fact (2 ≤ d)] in
/-- The forward composition: act g (euclidean_pullback g x) = x. -/
lemma act_euclidean_pullback (g : E d) (x : SpaceTime d) :
    act g (euclidean_pullback g x) = x := by
  simp only [euclidean_pullback_eq_inv_act]
  simpa using act_inv_general (g := g⁻¹) x

/-! ## Change of variables for the bilinear form -/

/-- The Euclidean action as a measurable equivalence. -/
noncomputable def actEquiv (g : E d) : SpaceTime d ≃ᵐ SpaceTime d where
  toFun := act g
  invFun := act g⁻¹
  left_inv x := act_inv_general g x
  right_inv x := by simpa using act_inv_general (g := g⁻¹) x
  measurable_toFun := (measurePreserving_act g).measurable
  measurable_invFun := (measurePreserving_act g⁻¹).measurable

omit [Fact (2 ≤ d)] in
/-- Measure-preserving property of actEquiv. -/
lemma measurePreserving_actEquiv (g : E d) :
    MeasurePreserving (actEquiv g) volume volume :=
  measurePreserving_act g

/-! ## Main theorem: Bilinear form invariance -/

set_option linter.unusedSectionVars false in
/-- The complex bilinear covariance form is invariant under Euclidean transformations:
    ⟨g•f, C(g•h)⟩ = ⟨f, Ch⟩.

    Proof: rewrite C(x,y) = C(g⁻¹•x, g⁻¹•y) by the kernel invariance
    `freeCovariance_euclidean_invariant` (`Covariance/ParsevalGeneric.lean`), then change
    variables u = g⁻¹•x, v = g⁻¹•y in the double integral — the Euclidean action preserves
    Lebesgue measure (`measurePreserving_act`), and `MeasurePreserving.prod` lifts this to
    the product space. -/
theorem freeCovarianceℂ_bilinear_euclidean_invariant (g : E d) (f h : SchwartzTestFunctionℂ d) :
    freeCovarianceℂ_bilinear m (euclidean_action g f) (euclidean_action g h) =
    freeCovarianceℂ_bilinear m f h := by
  unfold freeCovarianceℂ_bilinear
  simp only [euclidean_action_apply]
  -- Goal: ∫∫ f(g⁻¹•x) C(x,y) h(g⁻¹•y) dx dy = ∫∫ f(u) C(u,v) h(v) du dv
  -- Step 1: Rewrite C(x,y) using the identity x = g•(g⁻¹•x)
  have h_rewrite : ∀ x y, freeCovariance d m x y =
      freeCovariance d m (act g (euclidean_pullback g x)) (act g (euclidean_pullback g y)) := by
    intro x y
    simp only [act_euclidean_pullback]
  -- Step 2: Apply freeCovariance_euclidean_invariant
  conv_lhs =>
    arg 2; ext x; arg 2; ext y
    rw [h_rewrite x y, freeCovariance_euclidean_invariant]
  -- Now: ∫∫ f(g⁻¹•x) C(g⁻¹•x, g⁻¹•y) h(g⁻¹•y) dx dy = ∫∫ f(u) C(u,v) h(v) du dv
  -- Step 3: Change variables using measure-preserving property
  -- Use the measure-preserving property of actEquiv g
  -- Key: actEquiv g sends u ↦ g•u, so (g⁻¹•(g•u)) = u
  have h_mp := measurePreserving_actEquiv g
  -- MeasurePreserving.integral_comp' h_mp G says: ∫ u, G(g•u) = ∫ x, G x
  -- For the outer integral:
  -- LHS = ∫ x, G x where G x = inner integral with g⁻¹•x
  -- We want ∫ u, G(g•u) = ∫ u, (inner integral with g⁻¹•(g•u)) = ∫ u, (inner integral with u)
  conv_lhs =>
    arg 2; ext x
    rw [← euclidean_pullback_act g x]
  rw [(MeasurePreserving.integral_comp' h_mp _).symm]
  simp only [actEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, euclidean_pullback_act]
  -- Now rewrite inner integral for each fixed u
  congr 1
  funext u
  conv_lhs =>
    arg 2; ext y
    rw [← euclidean_pullback_act g y]
  rw [(MeasurePreserving.integral_comp' h_mp _).symm]
  simp only [actEquiv, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, euclidean_pullback_act]

/-- The free GFF measure satisfies the complex covariance Euclidean invariance property.
    This removes the `h_euc` hypothesis from the master theorem. -/
theorem CovarianceEuclideanInvariantℂ_μ_GFF :
    CovarianceEuclideanInvariantℂ (gaussianFreeField_free (d := d) m) := by
  intro g f h
  -- Reduce SchwingerFunctionℂ₂ to freeCovarianceℂ_bilinear via the Gaussian structure
  rw [gff_two_point_equals_covarianceℂ_free, gff_two_point_equals_covarianceℂ_free]
  exact freeCovarianceℂ_bilinear_euclidean_invariant m g f h

end QFT

end
