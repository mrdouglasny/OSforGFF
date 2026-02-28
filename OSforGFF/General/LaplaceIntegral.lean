/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Proof of the Laplace Integral Identity (Bessel K_{1/2})

This file proves the integral identity:
  ∫₀^∞ s^{-1/2} exp(-a/s - b*s) ds = √(π/b) exp(-2√(ab))

This is a special case of the modified Bessel function K_{1/2} identity.

## Proof Strategy

1. **Substitution s = t²**: Transforms s^{-1/2} ds to 2 dt
2. **Complete the square**: a/t² + bt² = (√a/t - √b·t)² + 2√(ab)
3. **Factor out exp(-2√(ab))**
4. **Substitution u = √b·t**: Reduces to ∫ exp(-(c/u - u)²) du where c = √(ab)
5. **Glasser/Cauchy-Schlömilch**: Show ∫₀^∞ exp(-(c/u - u)²) du = √π/2
6. **Combine**: Get the final result

## References

- Gradshteyn & Ryzhik, Table of Integrals, Entry 3.471.9
- DLMF §10.32.10 (Modified Bessel functions)
- Glasser, M.L. "A remarkable property of definite integrals" (1983)
-/

open Real Set MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace LaplaceIntegral

/-! ## Part 2: The Glasser/Cauchy-Schlömilch Identity

The key identity is: for c > 0,
  ∫₀^∞ exp(-(c/u - u)²) du = √π / 2

Note: we use (c/u - u) not (u - c/u) to match the form after our substitutions.
Since (c/u - u)² = (u - c/u)², these are equivalent.
-/

/-- The Glasser quadratic form is symmetric: (c/u - u)² = (u - c/u)² -/
lemma glasser_sq_symm (c u : ℝ) : (c / u - u)^2 = (u - c / u)^2 := by ring

/-- Expansion: (c/u - u)² = c²/u² - 2c + u² -/
lemma glasser_expand (c u : ℝ) (hu : u ≠ 0) : (c / u - u)^2 = c^2 / u^2 - 2*c + u^2 := by
  field_simp; ring

/-- Lower bound: (c/u - u)² ≥ u² - 2c -/
lemma glasser_lower_bound (c u : ℝ) (hu : u ≠ 0) : (c / u - u)^2 ≥ u^2 - 2*c := by
  rw [glasser_expand c u hu]; have : 0 ≤ c^2 / u^2 := div_nonneg (sq_nonneg c) (sq_nonneg u); linarith


/-- The derivative of u ↦ c/u - u is -c/u² - 1 -/
lemma hasDerivAt_glasser_map (c : ℝ) (u : ℝ) (hu : u ≠ 0) :
    HasDerivAt (fun x => c / x - x) (-c / u^2 - 1) u := by
  convert ((hasDerivAt_inv hu).const_mul c).sub (hasDerivAt_id u) using 1; field_simp

/-! ## Part 3: The core Glasser integral

This is the key technical result. The proof uses the remarkable fact that
the substitution v = c/u, combined with appropriate symmetry arguments,
reduces the integral to a Gaussian.

**Proof idea**:
Let I = ∫₀^∞ exp(-(c/u - u)²) du.

Substitute v = c/u in I:
- When u → 0⁺, v → ∞; when u → ∞, v → 0⁺
- du = -c/v² dv
- c/u - u = c/(c/v) - c/v = v - c/v = -(c/v - v)

So I = ∫_∞^0 exp(-(-(c/v - v))²) (-c/v²) dv
     = ∫_0^∞ exp(-(c/v - v)²) (c/v²) dv

Adding these:
2I = ∫_0^∞ exp(-(c/u - u)²) (1 + c/u²) du

Note that d/du(c/u - u) = -c/u² - 1 = -(1 + c/u²), so |d/du(c/u - u)| = 1 + c/u².

Thus 2I = ∫_0^∞ exp(-(c/u - u)²) |d/du(c/u - u)| du

Substituting w = c/u - u (which maps (0,∞) → ℝ bijectively):
2I = ∫_{-∞}^{+∞} exp(-w²) dw = √π

Therefore I = √π/2.
-/
/-- The substitution u ↦ c/u shows that the Glasser integral is invariant under
    multiplication by c/u². This is the key identity that enables the proof. -/
lemma glasser_integral_substitution_identity (c : ℝ) (hc : 0 < c) :
    ∫ u in Ioi 0, exp (-(c/u - u)^2) =
    ∫ u in Ioi 0, (c/u^2) * exp (-(c/u - u)^2) := by
  -- Use change of variables with f(u) = c/u
  have h_image : (fun u => c / u) '' (Ioi 0) = Ioi 0 := by
    ext v; simp only [mem_image, mem_Ioi]
    constructor
    · rintro ⟨u, hu, rfl⟩; exact div_pos hc hu
    · intro hv; exact ⟨c / v, div_pos hc hv, by field_simp⟩
  have h_inj : InjOn (fun u => c / u) (Ioi 0) := fun x hx y hy hxy => by
    simp only [mem_Ioi] at hx hy; field_simp at hxy; nlinarith [mul_pos hx hy]
  have h_deriv : ∀ u ∈ Ioi 0, HasDerivWithinAt (fun u => c / u) (-c / u^2) (Ioi 0) u := fun u hu =>
    (((hasDerivAt_inv (ne_of_gt hu)).const_mul c).hasDerivWithinAt).congr_deriv (by field_simp)
  let g : ℝ → ℝ := fun v => exp (-(c/v - v)^2)
  have h_cov := @integral_image_eq_integral_abs_deriv_smul ℝ _ _
      (Ioi 0) (fun u => c / u) (fun u => -c / u^2)
      measurableSet_Ioi h_deriv h_inj g
  rw [h_image] at h_cov
  have h_simp : ∀ u ∈ Ioi 0, |-c / u^2| * g (c / u) = (c / u^2) * exp (-(c/u - u)^2) := fun u hu => by
    have hu_pos : 0 < u := hu
    rw [abs_of_neg (div_neg_of_neg_of_pos (by linarith) (sq_pos_of_pos hu_pos))]
    simp only [g]; congr 2
    · ring
    · have h_eq : c / (c / u) - c / u = u - c / u := by field_simp [ne_of_gt hu_pos]
      rw [h_eq, ← glasser_sq_symm]
  simp only [smul_eq_mul, g] at h_cov ⊢
  rw [setIntegral_congr_fun measurableSet_Ioi h_simp] at h_cov
  exact h_cov

/-- Split (0, ∞) = (0, 1] ∪ (1, ∞) -/
private lemma Ioi_zero_eq_Ioc_union_Ioi : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := by
  ext x; simp only [mem_union, mem_Ioi, mem_Ioc]
  constructor
  · intro hx; by_cases h : x ≤ 1 <;> [exact .inl ⟨hx, h⟩; exact .inr (not_le.mp h)]
  · intro h; cases h with | inl h => exact h.1 | inr h => exact lt_trans one_pos h

/-- The Glasser integrand is integrable on (0, ∞).
    Proof: On (0, 1], bounded by 1 on finite measure set.
           On (1, ∞), dominated by e^{2c} · e^{-u²} which is Gaussian-integrable. -/
theorem glasser_integrable (c : ℝ) (_hc : 0 < c) :
    IntegrableOn (fun u => exp (-(c/u - u)^2)) (Ioi 0) := by
  rw [Ioi_zero_eq_Ioc_union_Ioi]
  apply IntegrableOn.union
  · -- On (0, 1]: bounded by 1 on a finite measure set
    have h_meas : volume (Ioc (0 : ℝ) 1) < ⊤ := by
      simp only [Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, ENNReal.one_lt_top]
    have h_contOn : ContinuousOn (fun u : ℝ => exp (-(c/u - u)^2)) (Ioc 0 1) := by
      apply Real.continuous_exp.comp_continuousOn
      apply ContinuousOn.neg; apply ContinuousOn.pow
      apply ContinuousOn.sub
      · exact continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt hx.1)
      · exact continuousOn_id
    refine IntegrableOn.of_bound h_meas (h_contOn.aestronglyMeasurable measurableSet_Ioc) 1 ?_
    filter_upwards with u
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
    exact exp_le_one_iff.mpr (neg_nonpos.mpr (sq_nonneg _))
  · -- On (1, ∞): dominated by e^{2c} · e^{-u²}
    have h_bound : ∀ u ∈ Ioi (1 : ℝ), ‖exp (-(c/u - u)^2)‖ ≤ ‖exp (2*c) * exp (-u^2)‖ := by
      intro u hu
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (exp_pos _) (exp_pos _))]
      have hu1 : 1 ≤ u := le_of_lt hu
      have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu1
      calc exp (-(c/u - u)^2)
          ≤ exp (-(u^2 - 2*c)) := exp_le_exp.mpr (neg_le_neg (glasser_lower_bound c u hu_pos.ne'))
        _ = exp (2*c - u^2) := by ring_nf
        _ = exp (2*c) * exp (-u^2) := by rw [← exp_add]; ring_nf
    have h_gauss_int : IntegrableOn (fun u => exp (2*c) * exp (-u^2)) (Ioi 1) := by
      have h1 : IntegrableOn (fun u => exp (-u^2)) (Ioi 0) := by
        simpa using integrableOn_Ioi_exp_neg_mul_sq_iff.mpr one_pos
      simpa [smul_eq_mul] using (h1.mono_set (Ioi_subset_Ioi one_pos.le)).smul (exp (2*c))
    have h_contOn : ContinuousOn (fun u : ℝ => exp (-(c/u - u)^2)) (Ioi 1) := by
      apply Real.continuous_exp.comp_continuousOn
      apply ContinuousOn.neg; apply ContinuousOn.pow
      apply ContinuousOn.sub
      · exact continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (lt_trans one_pos hx))
      · exact continuousOn_id
    have h_ae_bound : ∀ᵐ u ∂(volume.restrict (Ioi 1)),
        ‖exp (-(c/u - u)^2)‖ ≤ ‖exp (2*c) * exp (-u^2)‖ := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      apply ae_of_all; intro u hu; exact h_bound u hu
    exact Integrable.mono h_gauss_int (h_contOn.aestronglyMeasurable measurableSet_Ioi) h_ae_bound

/-- The weighted Glasser integrand is integrable on (0, ∞).
    Proof: Use change of variables v = c/u which maps (0,1] → [c,∞) and (1,∞) → (0,c].
    On each piece, the weighted integrand transforms to the unweighted one on a subset of (0,∞). -/
theorem glasser_weighted_integrable (c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun u => (c/u^2) * exp (-(c/u - u)^2)) (Ioi 0) := by
  rw [Ioi_zero_eq_Ioc_union_Ioi]
  apply IntegrableOn.union
  · -- On (0, 1]: Use change of variables v = c/u, which maps (0, 1] → [c, ∞)
    -- The key lemma is integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn:
    -- For antitone f with derivative f', IntegrableOn g (f '' s) ↔ IntegrableOn ((-f') • (g ∘ f)) s
    -- With f(u) = c/u (antitone), f'(u) = -c/u², -f'(u) = c/u²
    -- g(v) = exp(-(c/v - v)²), f '' (0,1] = [c, ∞)
    -- The RHS is IntegrableOn (fun u => (c/u²) * exp(-(c/(c/u) - c/u)²)) (Ioc 0 1)
    --         = IntegrableOn (fun u => (c/u²) * exp(-(u - c/u)²)) (Ioc 0 1)
    --         = IntegrableOn (fun u => (c/u²) * exp(-(c/u - u)²)) (Ioc 0 1)  [since (a-b)² = (b-a)²]
    have h_base := glasser_integrable c hc
    -- The unweighted integrand is integrable on [c, ∞) ⊆ (0, ∞)
    have h_image : (fun u => c / u) '' (Ioc 0 1) = Ici c := by
      ext v; simp only [mem_image, mem_Ioc, mem_Ici]
      constructor
      · rintro ⟨u, ⟨hu_pos, hu_le⟩, rfl⟩
        have : c / u ≥ c / 1 := by
          apply div_le_div_of_nonneg_left (le_of_lt hc) hu_pos hu_le
        simp at this; exact this
      · intro hv
        have hv_pos : 0 < v := lt_of_lt_of_le hc hv
        use c / v
        constructor
        · constructor
          · exact div_pos hc hv_pos
          · rw [div_le_one hv_pos]; exact hv
        · field_simp
    have h_int_image : IntegrableOn (fun v => exp (-(c/v - v)^2)) (Ici c) := by
      apply h_base.mono_set
      intro v hv
      simp only [mem_Ici, mem_Ioi] at hv ⊢
      exact lt_of_lt_of_le hc hv
    -- f(u) = c/u is antitone on (0, 1]
    have h_anti : AntitoneOn (fun u => c / u) (Ioc 0 1) := by
      intro x hx y hy hxy
      simp only [mem_Ioc] at hx hy
      -- Need: c/y ≤ c/x when x ≤ y (since dividing by larger gives smaller)
      -- div_le_div_of_nonneg_left : 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c
      -- For a/b ≤ a/c with a=c, b=y, c=x: need 0 ≤ c, 0 < x, x ≤ y
      exact div_le_div_of_nonneg_left (le_of_lt hc) hx.1 hxy
    -- Derivative of f
    have h_deriv : ∀ u ∈ Ioc (0 : ℝ) 1, HasDerivWithinAt (fun u => c / u) (-c / u^2) (Ioc 0 1) u := by
      intro u hu
      have hu_ne : u ≠ 0 := ne_of_gt hu.1
      convert (HasDerivAt.const_mul c (hasDerivAt_inv hu_ne)).hasDerivWithinAt using 1
      field_simp
    -- Apply the key change of variables lemma for integrability
    rw [← h_image] at h_int_image
    have h_cov := integrableOn_image_iff_integrableOn_deriv_smul_of_antitoneOn
        measurableSet_Ioc h_deriv h_anti (fun v => exp (-(c/v - v)^2))
    -- The transformed integrand: (-f'(u)) • g(f(u)) = (c/u²) • exp(-(c/(c/u) - c/u)²)
    -- Need to show this equals (c/u²) * exp(-(c/u - u)²)
    have h_eq : (fun u => (-(-c / u^2)) • exp (-(c/(c/u) - c/u)^2)) =
        (fun u => (c/u^2) * exp (-(c/u - u)^2)) := by
      ext u
      simp only [smul_eq_mul]
      by_cases hu : u = 0
      · simp [hu]
      · -- First: -(-c/u²) = c/u²
        have h_neg : -(-c / u^2) = c / u^2 := by ring
        rw [h_neg]
        -- Second: exp(-(c/(c/u) - c/u)²) = exp(-(c/u - u)²)
        congr 1
        -- c/(c/u) = u when u ≠ 0
        have h1 : c / (c / u) = u := by field_simp
        rw [h1]
        -- (u - c/u)² = (c/u - u)² since (a-b)² = (b-a)²
        congr 2
        ring
    rw [h_eq] at h_cov
    exact h_cov.mp h_int_image
  · -- On (1, ∞): c/u² ≤ c, dominated by c · e^{2c} · e^{-u²}
    have h_bound : ∀ u ∈ Ioi (1 : ℝ),
        ‖(c/u^2) * exp (-(c/u - u)^2)‖ ≤ ‖c * exp (2*c) * exp (-u^2)‖ := by
      intro u hu
      have hu1 : 1 ≤ u := le_of_lt hu
      have hu_pos : 0 < u := lt_of_lt_of_le one_pos hu1
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (div_pos hc (sq_pos_of_pos hu_pos)) (exp_pos _))]
      rw [Real.norm_eq_abs, abs_of_pos (mul_pos (mul_pos hc (exp_pos _)) (exp_pos _))]
      have h_cu2 : c / u^2 ≤ c := by
        have h_u2_ge_1 : 1 ≤ u^2 := by nlinarith
        -- div_le_div_of_nonneg_left : 0 ≤ a → 0 < c → c ≤ b → a / b ≤ a / c
        -- For c/u² ≤ c/1: a=c, b=u², c=1. Need: 0 ≤ c, 0 < 1, 1 ≤ u²
        calc c / u^2 ≤ c / 1 := div_le_div_of_nonneg_left (le_of_lt hc) one_pos h_u2_ge_1
          _ = c := div_one c
      have h_exp : exp (-(c/u - u)^2) ≤ exp (2*c) * exp (-u^2) :=
        calc exp (-(c/u - u)^2)
            ≤ exp (-(u^2 - 2*c)) := exp_le_exp.mpr (neg_le_neg (glasser_lower_bound c u hu_pos.ne'))
          _ = exp (2*c) * exp (-u^2) := by rw [← exp_add]; ring_nf
      calc c / u^2 * exp (-(c/u - u)^2)
          ≤ c * (exp (2*c) * exp (-u^2)) := by nlinarith [exp_pos (-(c/u - u)^2)]
        _ = c * exp (2*c) * exp (-u^2) := by ring
    have h_dom_int : IntegrableOn (fun u => c * exp (2*c) * exp (-u^2)) (Ioi 1) := by
      have h1 : IntegrableOn (fun u => exp (-u^2)) (Ioi 0) := by
        simpa using integrableOn_Ioi_exp_neg_mul_sq_iff.mpr one_pos
      simpa using (h1.mono_set (Ioi_subset_Ioi one_pos.le)).const_mul (c * exp (2*c))
    have h_contOn : ContinuousOn (fun u : ℝ => (c/u^2) * exp (-(c/u - u)^2)) (Ioi 1) := by
      apply ContinuousOn.mul
      · exact continuousOn_const.div (continuousOn_pow 2) (fun x hx => pow_ne_zero 2 (ne_of_gt (lt_trans one_pos hx)))
      · apply Real.continuous_exp.comp_continuousOn
        apply ContinuousOn.neg; apply ContinuousOn.pow
        apply ContinuousOn.sub
        · exact continuousOn_const.div continuousOn_id (fun x hx => ne_of_gt (lt_trans one_pos hx))
        · exact continuousOn_id
    have h_ae_bound : ∀ᵐ u ∂(volume.restrict (Ioi 1)),
        ‖(c/u^2) * exp (-(c/u - u)^2)‖ ≤ ‖c * exp (2*c) * exp (-u^2)‖ := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      apply ae_of_all; intro u hu; exact h_bound u hu
    exact Integrable.mono h_dom_int (h_contOn.aestronglyMeasurable measurableSet_Ioi) h_ae_bound

lemma glasser_integral_double (c : ℝ) (hc : 0 < c) :
    2 * ∫ u in Ioi 0, exp (-(c/u - u)^2) =
    ∫ u in Ioi 0, (1 + c/u^2) * exp (-(c/u - u)^2) := by
  rw [two_mul]; nth_rewrite 2 [glasser_integral_substitution_identity c hc]
  rw [← integral_add (glasser_integrable c hc) (glasser_weighted_integrable c hc)]
  exact setIntegral_congr_fun measurableSet_Ioi fun _ _ => by ring

/-- The Glasser map w = c/u - u tends to +∞ as u → 0⁺. -/
lemma glasser_tendsto_atTop_at_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun u => c / u - u) (𝓝[>] 0) atTop := by
  have h1 : Tendsto (fun (u : ℝ) => u⁻¹) (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := tendsto_inv_nhdsGT_zero
  have h2 : Tendsto (fun u => c * u⁻¹) (nhdsWithin (0 : ℝ) (Ioi 0)) atTop :=
    Filter.Tendsto.const_mul_atTop hc h1
  have h3 : Tendsto (fun u => c / u) (nhdsWithin (0 : ℝ) (Ioi 0)) atTop := by
    simp only [div_eq_mul_inv]; exact h2
  -- -u is bounded below by -1 on (0, 1)
  have h_bdd : ∀ᶠ u in nhdsWithin (0 : ℝ) (Ioi 0), (-1 : ℝ) ≤ -u := by
    rw [Filter.eventually_iff_exists_mem]
    use Ioo (0 : ℝ) 1
    constructor
    · rw [mem_nhdsWithin]; use Iio (1 : ℝ)
      refine ⟨isOpen_Iio, (zero_lt_one : (0 : ℝ) < 1), ?_⟩
      intro x hx
      simp only [mem_inter_iff, mem_Ioi, mem_Iio, mem_Ioo] at hx ⊢
      exact ⟨hx.2, hx.1⟩
    · intro u hu; simp only [mem_Ioo] at hu; linarith
  have h_eq : (fun u => c / u - u) = (fun u => (-u) + (c / u)) := by ext u; ring
  rw [h_eq]
  exact tendsto_atTop_add_left_of_le' _ (-1) h_bdd h3

/-- The Glasser map w = c/u - u tends to -∞ as u → +∞. -/
lemma glasser_tendsto_atBot_at_top (c : ℝ) (_hc : 0 < c) :
    Tendsto (fun u => c / u - u) atTop atBot := by
  have h1 : Tendsto (fun u => c / u) atTop (𝓝 0) := Filter.Tendsto.const_div_atTop tendsto_id c
  simpa [sub_eq_add_neg] using h1.add_atBot tendsto_neg_atTop_atBot

/-- The Glasser map is continuous on (0, ∞). -/
lemma glasser_continuousOn (c : ℝ) : ContinuousOn (fun u => c / u - u) (Ioi 0) :=
  (continuousOn_const.div continuousOn_id fun _ hu => ne_of_gt hu).sub continuousOn_id

/-- The Glasser map is strictly decreasing on (0, ∞). -/
lemma glasser_strictAntiOn (c : ℝ) (hc : 0 < c) : StrictAntiOn (fun u => c / u - u) (Ioi 0) := by
  intro x hx y hy hxy
  simp only [mem_Ioi] at hx hy
  have hx_ne : x ≠ 0 := ne_of_gt hx
  have hy_ne : y ≠ 0 := ne_of_gt hy
  -- Need: c/y - y < c/x - x
  -- Equivalently: c/x - c/y > x - y
  -- c(y - x)/(xy) > x - y
  -- Since x < y, y - x > 0 and x - y < 0
  -- c(y - x)/(xy) > 0 > x - y ✓
  have h1 : c / x - c / y = c * (y - x) / (x * y) := by field_simp
  have h2 : 0 < c * (y - x) / (x * y) := by
    apply div_pos
    · exact mul_pos hc (sub_pos.mpr hxy)
    · exact mul_pos hx hy
  have h3 : x - y < 0 := sub_neg_of_lt hxy
  calc c / y - y = c / x - (c / x - c / y) - y := by ring
    _ = c / x - c * (y - x) / (x * y) - y := by rw [h1]
    _ < c / x - 0 - y := by linarith
    _ = c / x - x + (x - y) := by ring
    _ < c / x - x + 0 := by linarith
    _ = c / x - x := by ring

/-- The Glasser map is injective on (0, ∞). -/
lemma glasser_injOn (c : ℝ) (hc : 0 < c) : InjOn (fun u => c / u - u) (Ioi 0) :=
  (glasser_strictAntiOn c hc).injOn

/-- The Glasser map has the stated derivative on (0, ∞). -/
lemma glasser_hasDerivWithinAt (c : ℝ) (u : ℝ) (hu : 0 < u) :
    HasDerivWithinAt (fun x => c / x - x) (-c / u^2 - 1) (Ioi 0) u :=
  (hasDerivAt_glasser_map c u hu.ne').hasDerivWithinAt

/-- The image of (0, ∞) under the Glasser map is all of ℝ. -/
lemma glasser_image_eq_univ (c : ℝ) (hc : 0 < c) :
    (fun u => c / u - u) '' (Ioi 0) = univ := by
  apply eq_univ_of_forall
  intro w
  let f := fun u => c / u - u
  have hcont := glasser_continuousOn c
  have htop := glasser_tendsto_atTop_at_zero c hc
  have hbot := glasser_tendsto_atBot_at_top c hc
  have h_at_sqrt : f (sqrt c) = 0 := by
    simp only [f]
    have h : sqrt c ≠ 0 := ne_of_gt (sqrt_pos.mpr hc)
    have h2 : c / sqrt c = sqrt c := by
      rw [div_eq_iff h, ← sq]; exact (sq_sqrt (le_of_lt hc)).symm
    linarith
  have h_sqrt_pos : sqrt c ∈ Ioi 0 := sqrt_pos.mpr hc
  have hpc : IsPreconnected (Ioi (0 : ℝ)) := isPreconnected_Ioi
  have hatTop_le : (atTop : Filter ℝ) ≤ 𝓟 (Ioi 0) := le_principal_iff.mpr (Ioi_mem_atTop 0)
  by_cases hw : w ≤ 0
  · -- Case w ≤ 0: use IVT from √c to +∞ (where f goes from 0 to -∞)
    haveI : (atTop : Filter ℝ).NeBot := atTop_neBot
    have h_ivt : Iic (f (sqrt c)) ⊆ f '' Ioi 0 :=
      hpc.intermediate_value_Iic h_sqrt_pos hatTop_le hcont hbot
    rw [h_at_sqrt] at h_ivt
    exact h_ivt (mem_Iic.mpr hw)
  · -- Case w > 0: use IVT from 0⁺ to √c (where f goes from +∞ to 0)
    push_neg at hw
    haveI : (nhdsWithin (0 : ℝ) (Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
    have hnhds_le : nhdsWithin (0 : ℝ) (Ioi 0) ≤ 𝓟 (Ioi 0) :=
      inf_le_right.trans (le_refl _)
    have h_ivt : Ici (f (sqrt c)) ⊆ f '' Ioi 0 :=
      hpc.intermediate_value_Ici h_sqrt_pos hnhds_le hcont htop
    rw [h_at_sqrt] at h_ivt
    exact h_ivt (mem_Ici.mpr (le_of_lt hw))

/-- The absolute value of the Glasser map derivative is 1 + c/u². -/
lemma glasser_deriv_abs (c : ℝ) (hc : 0 < c) (u : ℝ) (hu : u ∈ Ioi 0) :
    |(-c / u^2 - 1)| = 1 + c / u^2 := by
  have h : 0 < c / u^2 := div_pos hc (sq_pos_of_pos hu)
  rw [show -c / u^2 = -(c / u^2) by ring, abs_of_neg (by linarith)]; ring

/-- The weighted integral equals √π via change of variables w = c/u - u.
    This is the core analytical step. -/
theorem weighted_glasser_integral_eq_gaussian (c : ℝ) (hc : 0 < c) :
    ∫ u in Ioi 0, (1 + c/u^2) * exp (-(c/u - u)^2) = sqrt π := by
  -- Use change of variables: w = c/u - u
  -- The Jacobian |dw/du| = |−c/u² − 1| = 1 + c/u²
  -- So ∫ (1 + c/u²) exp(-(c/u - u)²) du = ∫ |dw/du| exp(-w²) du = ∫ exp(-w²) dw = √π
  let f := fun u => c / u - u
  let f' := fun u => -c / u^2 - 1
  let g := fun w => exp (-w^2)
  -- Apply change of variables formula
  have h_cov := @integral_image_eq_integral_abs_deriv_smul ℝ _ _ (Ioi 0) f f'
    measurableSet_Ioi (fun u hu => glasser_hasDerivWithinAt c u hu) (glasser_injOn c hc) g
  -- Rewrite using the image = ℝ
  have h_image := glasser_image_eq_univ c hc
  rw [h_image] at h_cov
  -- The LHS of h_cov is ∫_ℝ exp(-w²) = √π
  have h_gaussian : ∫ w : ℝ, exp (-w^2) = sqrt π := by
    have h := integral_gaussian (1 : ℝ)
    simp only [div_one] at h
    convert h using 2
    ext w
    simp only [one_mul, neg_mul]
  -- Transform h_cov: ∫_ℝ g = ∫_{Ioi 0} |f'| • (g ∘ f)
  -- i.e., √π = ∫_{Ioi 0} |f' u| * exp(-(c/u - u)²)
  simp only [smul_eq_mul, f, f', g] at h_cov
  -- Substitute the absolute value
  have h_abs : ∀ u ∈ Ioi 0, |-c / u^2 - 1| * exp (-(c / u - u)^2) =
      (1 + c / u^2) * exp (-(c / u - u)^2) := by
    intro u hu
    rw [glasser_deriv_abs c hc u hu]
  rw [setIntegral_congr_fun measurableSet_Ioi h_abs] at h_cov
  -- Now h_cov : ∫ w, exp(-w²) = ∫ u in Ioi 0, (1 + c/u²) * exp(-(c/u - u)²)
  rw [← h_cov, Measure.restrict_univ, h_gaussian]

theorem glasser_gaussian_integral (c : ℝ) (hc : 0 < c) :
    ∫ u in Ioi 0, exp (-(c/u - u)^2) = sqrt π / 2 := by
  linarith [glasser_integral_double c hc, weighted_glasser_integral_eq_gaussian c hc]

/-! ## Part 4: Completing the square -/

/-- Completing the square: a/t² + b·t² = (√a/t - √b·t)² + 2√(ab) -/
lemma complete_square (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (t : ℝ) (ht : 0 < t) :
    a / t^2 + b * t^2 = (sqrt a / t - sqrt b * t)^2 + 2 * sqrt (a * b) := by
  have expand : (sqrt a / t - sqrt b * t)^2 = a / t^2 - 2 * sqrt a * sqrt b + b * t^2 := by
    field_simp; ring_nf; rw [sq_sqrt ha.le, sq_sqrt hb.le]; ring
  rw [expand, Real.sqrt_mul ha.le b]; ring

/-! ## Part 5: The main substitutions -/

/-- First substitution: s = t² transforms s^{-1/2} ds to 2 dt -/
lemma laplace_integral_subst_sq (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b) :
    ∫ s in Ioi 0, s^(-(1/2 : ℝ)) * exp (-a/s - b*s) =
    2 * ∫ t in Ioi 0, exp (-a/t^2 - b*t^2) := by
  have h2pos : (0 : ℝ) < 2 := two_pos
  have h := @integral_comp_rpow_Ioi_of_pos ℝ _ _
    (fun s => s^(-(1/2 : ℝ)) * exp (-a/s - b*s)) 2 h2pos
  simp only [smul_eq_mul] at h
  rw [← h]
  -- The LHS integrand is: 2 * t^(2-1) * ((t²)^(-1/2) * exp(-a/t² - b*t²))
  -- Simplify to: 2 * exp(-a/t² - b*t²)
  -- Then pull out the 2
  rw [← integral_const_mul 2]
  -- Use setIntegral_congr_fun to only prove equality on Ioi 0
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  -- Now t ∈ Ioi 0, i.e., t > 0
  have ht_pos : 0 < t := mem_Ioi.mp ht
  have ht_ne : t ≠ 0 := ne_of_gt ht_pos
  have ht_nonneg : 0 ≤ t := le_of_lt ht_pos
  -- Simplify t^(2-1) = t
  have h1 : (t : ℝ) ^ ((2 : ℝ) - 1) = t := by
    rw [show (2 : ℝ) - 1 = 1 by norm_num, rpow_one]
  rw [h1]
  -- Key: (t^2)^(-1/2) = t⁻¹
  have key : (t ^ (2 : ℝ)) ^ (-(1/2) : ℝ) = t⁻¹ := by
    rw [← rpow_mul ht_nonneg]
    norm_num
    exact rpow_neg_one t
  simp only [key]
  -- Goal: 2 * t * (t⁻¹ * exp(...)) = 2 * exp(...)
  -- Rearrange: (2 * t) * (t⁻¹ * E) = 2 * (t * t⁻¹) * E = 2 * E
  -- Direct calculation using field_simp
  field_simp
  -- Need: (t^2)^2 = t^4 and the expressions to match
  congr 1
  -- Use field_simp to clear denominators, then ring
  have htsq_ne : (t : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 ht_ne
  field_simp [htsq_ne, ht_ne]
  -- The issue is t ^ (2 : ℕ) vs t ^ (2 : ℝ) (natural power vs rpow)
  -- For positive t, these are equal but not definitionally
  have h_pow_eq : (t : ℝ) ^ (2 : ℕ) = t ^ (2 : ℝ) := (rpow_natCast t 2).symm
  simp only [h_pow_eq]
  -- Goal: (-a - (t^2)^2 * b) * t^2 = t^2 * (-a - b * t^4)
  -- Use: (t^2)^2 = t^4
  -- We need to show: (-a - (t^2)^2 * b) * t^2 = t^2 * (-a - b * t^4)
  -- Both sides equal -a*t^2 - b*t^6
  -- The goal involves both rpow (t ^ (2:ℝ)) and nat power (t ^ 2)
  -- We need to convert all to nat powers for ring to work
  have h_rpow_nat : (t : ℝ) ^ (2 : ℝ) = t ^ (2 : ℕ) := rpow_natCast t 2
  simp only [h_rpow_nat]
  -- Now all powers should be natural, ring can solve
  ring

/-- After completing the square, factor out exp(-2√(ab)) -/
lemma laplace_integral_factor (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioi 0, exp (-a/t^2 - b*t^2) =
    exp (-2 * sqrt (a * b)) * ∫ t in Ioi 0, exp (-(sqrt a / t - sqrt b * t)^2) := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [show -a/t^2 - b*t^2 = -(a/t^2 + b*t^2) by ring, complete_square a b ha hb t ht, neg_add, exp_add]
  ring_nf

/-- Second substitution: u = √b · t, so √a/t - √b·t = √(ab)/u - u -/
lemma laplace_integral_subst_scale (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ t in Ioi 0, exp (-(sqrt a / t - sqrt b * t)^2) =
    (1 / sqrt b) * ∫ u in Ioi 0, exp (-(sqrt (a * b) / u - u)^2) := by
  have hsb : 0 < sqrt b := sqrt_pos.mpr hb
  have h := @integral_comp_mul_left_Ioi ℝ _ _ (fun u => exp (-(sqrt (a * b) / u - u)^2)) 0 (sqrt b) hsb
  simp only [mul_zero, smul_eq_mul, inv_eq_one_div] at h ⊢
  rw [← h]; refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  rw [sqrt_mul ha.le b]; field_simp [hsb.ne', (mem_Ioi.mp ht).ne']

/-! ## Part 6: The main theorem -/

/-- **Main Theorem**: The Laplace integral identity (Bessel K_{1/2}).

    ∫₀^∞ s^{-1/2} exp(-a/s - b*s) ds = √(π/b) exp(-2√(ab))

    This is Gradshteyn & Ryzhik 3.471.9 with ν = 1/2.
-/
theorem laplace_integral_half_power (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ s in Ioi 0, s^(-(1/2 : ℝ)) * exp (-a/s - b*s) =
    sqrt (π / b) * exp (-2 * sqrt (a * b)) := by
  rw [laplace_integral_subst_sq a b ha hb, laplace_integral_factor a b ha hb,
      laplace_integral_subst_scale a b ha hb,
      glasser_gaussian_integral _ (sqrt_pos.mpr (mul_pos ha hb)),
      sqrt_div pi_pos.le b]
  ring

/-- **Extension**: The Laplace integral identity for a ≥ 0 (extends to include a = 0).

    When a = 0, the integral reduces to the Gamma function:
      ∫₀^∞ s^{-1/2} exp(-b·s) ds = Γ(1/2) / √b = √(π/b)

    which matches √(π/b) · exp(-2√(0·b)) = √(π/b) · 1 = √(π/b).
-/
theorem laplace_integral_half_power_nonneg (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    ∫ s in Ioi 0, s^(-(1/2 : ℝ)) * exp (-a/s - b*s) =
    sqrt (π / b) * exp (-2 * sqrt (a * b)) := by
  rcases ha.eq_or_lt with rfl | ha_pos
  · -- Case a = 0: reduces to Gamma(1/2) integral
    -- First simplify the integrand: -0/s - b*s = -b*s
    have h_integrand : ∀ s ∈ Ioi (0:ℝ), s^(-(1/2 : ℝ)) * exp (-(0:ℝ)/s - b*s) =
        s^((1/2 : ℝ) - 1) * exp (-(b * s)) := by
      intro s _
      congr 1
      · norm_num  -- -1/2 = 1/2 - 1
      · ring_nf   -- -0/s - b*s = -(b*s)
    rw [setIntegral_congr_fun measurableSet_Ioi h_integrand]
    -- Goal: ∫ s in Ioi 0, s^(1/2 - 1) * exp(-(b*s)) = sqrt(π/b) * exp(-2*sqrt(0*b))
    -- Use integral_rpow_mul_exp_neg_mul_Ioi with exponent 1/2
    have h_half_pos : (0 : ℝ) < 1/2 := by norm_num
    have h := integral_rpow_mul_exp_neg_mul_Ioi h_half_pos hb
    -- h : ∫ t in Ioi 0, t^(1/2 - 1) * exp(-(b * t)) = (1/b)^(1/2) * Γ(1/2)
    rw [h, Real.Gamma_one_half_eq]
    -- Now: (1/b)^(1/2) * sqrt(π) = sqrt(π/b) * exp(-2*sqrt(0*b))
    -- Since sqrt(0*b) = 0 and exp(0) = 1
    simp only [zero_mul, sqrt_zero, mul_zero, exp_zero, mul_one]
    -- Goal: (1/b)^(1/2) * sqrt(π) = sqrt(π/b)
    -- Use: (1/b)^(1/2) = 1/sqrt(b) and sqrt(π/b) = sqrt(π)/sqrt(b)
    rw [one_div, ← sqrt_eq_rpow, sqrt_inv, sqrt_div pi_pos.le]
    ring
  · -- Case a > 0: use existing theorem
    exact laplace_integral_half_power a b ha_pos hb

end LaplaceIntegral
