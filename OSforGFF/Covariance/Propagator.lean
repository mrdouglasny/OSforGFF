/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform

/-!
# The `GFFPropagator` typeclass and the generic proper-time covariance

The dimension-generic seam of the OS-for-GFF library. The genuine per-`d` datum of the free
covariance is its radial closed form `Cprofile` (4D `(m/4π²r)K₁(mr)`; 3D `e^{-mr}/(4πr)`;
2D `(1/2π)K₀(mr)`). This file isolates it behind a two-field typeclass:

* `Cprofile : ℝ → ℝ` — the per-`d` radial profile;
* `schwinger_eq` — it equals, for `r > 0`, the **generic** proper-time (Schwinger/heat-kernel)
  integral `properTimeCovariance`, which is one uniform formula for every `d`.

Consequences that hold for every `d` are stated once as facts about `properTimeCovariance` and
transported to `Cprofile` through `schwinger_eq`: `L¹`-integrability (`GFFPropagator.integrable`) and
pointwise exponential decay (`GFFPropagator.decayBound`). The momentum-space propagator
`freePropagatorMom d m k = 1/((2π)²‖k‖²+m²)` is the forward Fourier transform of
`x ↦ properTimeCovariance d m ‖x‖`.

The position-space kernel of the theory is `freeCovariance d m x y := Cprofile ‖x − y‖`,
symmetric and invariant under simultaneous isometries of both arguments by radiality.
Instances (`Instances/`) provide the closed form and its Schwinger-integral evaluation;
everything else in the library consumes only the class.
-/

open MeasureTheory Real Complex
open scoped RealInnerProductSpace

namespace OSforGFF

noncomputable section

/-- Heat-kernel radial profile in `d` dimensions: `H_d(t, r) = (4πt)^{-d/2} · e^{-r²/(4t)}`.
    Its `d`-dimensional Fourier transform (in `x`, at `‖x‖ = r`) is the momentum Gaussian
    `e^{-t(2π)²‖k‖²}` — the `(4πt)^{-d/2}` cancels the Gaussian-integral normalization. -/
def heatKernelProfile (d : ℕ) (t r : ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t))

/-- The proper-time (Schwinger) form of the free covariance profile, uniform in `d`:
    `C_S(r) = ∫₀^∞ e^{-t m²} · (4πt)^{-d/2} · e^{-r²/(4t)} dt`.
    It is `L¹`, has pointwise exponential decay, and its forward Fourier transform (as
    `x ↦ C_S ‖x‖`) is the momentum propagator `1/((2π)²‖k‖² + m²)`. -/
def properTimeCovariance (d : ℕ) (m r : ℝ) : ℝ :=
  ∫ t in Set.Ioi 0, Real.exp (-t * m ^ 2) * heatKernelProfile d t r

/-- The momentum-space free propagator in mathlib's unitary Fourier convention:
    `P_d(k) = 1/((2π)²‖k‖² + m²)`. This is the forward Fourier transform of
    `fun x => properTimeCovariance d m ‖x‖`. -/
def freePropagatorMom (d : ℕ) (m : ℝ) (k : EuclideanSpace ℝ (Fin d)) : ℝ :=
  1 / ((2 * Real.pi) ^ 2 * ‖k‖ ^ 2 + m ^ 2)

/-! ### Derived facts about the generic heat kernel and proper-time covariance -/

/-- The heat-kernel profile factors its constant and time dependence (for `t > 0`):
    `H_d(t, r) = (4π)^{-d/2} · t^{-d/2} · e^{-r²/(4t)}`. -/
lemma heatKernelProfile_eq (d : ℕ) (t : ℝ) (ht : 0 < t) (r : ℝ) :
    heatKernelProfile d t r =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t)) := by
  unfold heatKernelProfile
  rw [Real.mul_rpow (by positivity) ht.le]

/-- The proper-time covariance with the dimension constant `(4π)^{-d/2}` pulled out of the
    integral: `C_S(r) = (4π)^{-d/2} · ∫₀^∞ t^{-d/2} e^{-m²t - r²/(4t)} dt`. Each instance evaluates
    the remaining `t`-integral to its closed form. -/
lemma properTimeCovariance_const_mul (d : ℕ) (m r : ℝ) :
    properTimeCovariance d m r =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) *
        ∫ t in Set.Ioi 0, t ^ (-(d : ℝ) / 2) * Real.exp (-m ^ 2 * t - r ^ 2 / (4 * t)) := by
  rw [properTimeCovariance, ← MeasureTheory.integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  have ht0 : (0 : ℝ) < t := ht
  rw [heatKernelProfile_eq d t ht0 r,
      show -m ^ 2 * t - r ^ 2 / (4 * t) = -t * m ^ 2 + -r ^ 2 / (4 * t) by ring, Real.exp_add]
  ring

/-- The heat-kernel normalization `∫ H_d(t, ‖z‖) dz = 1`, for every `d`: the `(4πt)^{-d/2}`
    prefactor cancels the Gaussian-integral normalization `(π/(1/4t))^{d/2} = (4πt)^{d/2}`. -/
lemma heatKernelProfile_integral_eq_one (d : ℕ) (t : ℝ) (ht : 0 < t) :
    ∫ z : EuclideanSpace ℝ (Fin d), heatKernelProfile d t ‖z‖ = 1 := by
  unfold heatKernelProfile
  have h_exp_eq : ∀ z : EuclideanSpace ℝ (Fin d),
      Real.exp (-‖z‖ ^ 2 / (4 * t)) = Real.exp (-(1 / (4 * t)) * ‖z‖ ^ 2) := by
    intro z; congr 1; field_simp
  simp_rw [h_exp_eq]
  rw [MeasureTheory.integral_const_mul]
  have hb : 0 < (1 / (4 * t)) := by positivity
  have h_gauss := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin d)) hb
  rw [h_gauss, finrank_euclideanSpace_fin]
  have h_div_eq : π / (1 / (4 * t)) = 4 * π * t := by field_simp
  rw [h_div_eq]
  have h_pos : 0 < 4 * π * t := by positivity
  rw [show (-(d : ℝ) / 2) = -((d : ℝ) / 2) by ring, Real.rpow_neg (le_of_lt h_pos)]
  rw [inv_mul_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos h_pos _))]

/-- The `d`-dimensional Fourier transform of the heat kernel is the momentum Gaussian:
    `𝓕[fun x => H_d(t, ‖x‖)](k) = e^{-4π²t‖k‖²} = e^{-t(2π)²‖k‖²}`. The dimension `d` cancels
    between the `(4πt)^{-d/2}` prefactor and the Gaussian-FT normalization `(4πt)^{d/2}`. -/
lemma heatKernelProfile_fourier (d : ℕ) (t : ℝ) (ht : 0 < t) (k : EuclideanSpace ℝ (Fin d)) :
    FourierTransform.fourier
        (fun x : EuclideanSpace ℝ (Fin d) => (heatKernelProfile d t ‖x‖ : ℂ)) k
      = Complex.exp (-(4 * Real.pi ^ 2 * t : ℝ) * ‖k‖ ^ 2) := by
  have hfun : (fun x : EuclideanSpace ℝ (Fin d) => (heatKernelProfile d t ‖x‖ : ℂ))
      = (((4 * Real.pi * t) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
          (fun x : EuclideanSpace ℝ (Fin d) => Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * ‖x‖ ^ 2)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold heatKernelProfile
    rw [Complex.ofReal_mul]
    congr 1
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hfun]
  have hsmul : FourierTransform.fourier
        ((((4 * Real.pi * t) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
          (fun x : EuclideanSpace ℝ (Fin d) => Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * ‖x‖ ^ 2)))
      = (((4 * Real.pi * t) ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
          FourierTransform.fourier
            (fun x : EuclideanSpace ℝ (Fin d) => Complex.exp (-((1 / (4 * t) : ℝ) : ℂ) * ‖x‖ ^ 2)) :=
    VectorFourier.fourierIntegral_const_smul _ _ _ _ _
  rw [hsmul, Pi.smul_apply, smul_eq_mul]
  rw [fourier_gaussian_innerProductSpace (V := EuclideanSpace ℝ (Fin d))
        (b := ((1 / (4 * t) : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; positivity) k]
  rw [finrank_euclideanSpace_fin]
  have hpos : (0 : ℝ) < 4 * Real.pi * t := by positivity
  have hAne : ((4 * Real.pi * t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hpos)
  have hb : (Real.pi : ℂ) / ((1 / (4 * t) : ℝ) : ℂ) = ((4 * Real.pi * t : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [hb]
  have hpre : (((4 * Real.pi * t) ^ (-(d : ℝ) / 2) : ℝ) : ℂ)
      = ((4 * Real.pi * t : ℝ) : ℂ) ^ (-(d : ℂ) / 2) := by
    rw [Complex.ofReal_cpow (le_of_lt hpos)]; congr 1; push_cast; ring
  rw [hpre, ← mul_assoc, ← Complex.cpow_add _ _ hAne]
  rw [show (-(d : ℂ) / 2 + (d : ℂ) / 2) = 0 by ring, Complex.cpow_zero, one_mul]
  congr 1
  push_cast
  field_simp

/-- The heat-kernel profile is nonnegative for `t > 0`. -/
lemma heatKernelProfile_nonneg (d : ℕ) (t r : ℝ) (ht : 0 < t) : 0 ≤ heatKernelProfile d t r := by
  unfold heatKernelProfile
  have h4 : (0 : ℝ) < 4 * Real.pi * t := by positivity
  exact mul_nonneg (Real.rpow_nonneg (le_of_lt h4) _) (Real.exp_nonneg _)

/-- For `t > 0`, `x ↦ H_d(t, ‖x‖)` is integrable (a constant times a Gaussian). -/
lemma heatKernelProfile_integrable (d : ℕ) (t : ℝ) (ht : 0 < t) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => heatKernelProfile d t ‖x‖) := by
  unfold heatKernelProfile
  apply Integrable.const_mul
  have h := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := EuclideanSpace ℝ (Fin d))
    (b := ((1 / (4 * t) : ℝ) : ℂ)) (by rw [Complex.ofReal_re]; positivity) 0 0
  simp only [zero_mul, add_zero] at h
  refine (h.norm).congr ?_
  filter_upwards with x
  rw [Complex.norm_exp]
  congr 1
  rw [show (-((1 / (4 * t) : ℝ) : ℂ) * (↑‖x‖ : ℂ) ^ 2) = ((-‖x‖ ^ 2 / (4 * t) : ℝ) : ℂ) by
      push_cast; ring, Complex.ofReal_re]

/-- The proper-time covariance is nonnegative. -/
lemma properTimeCovariance_nonneg (d : ℕ) (m r : ℝ) : 0 ≤ properTimeCovariance d m r := by
  unfold properTimeCovariance
  apply setIntegral_nonneg measurableSet_Ioi
  intro t ht
  exact mul_nonneg (Real.exp_nonneg _) (heatKernelProfile_nonneg d t r ht)

/-- Joint integrability of the Schwinger integrand `(t, x) ↦ e^{-tm²} H_d(t, ‖x‖)` over
    `(volume|_{Ioi 0}) × volume`. -/
lemma schwinger_prod_integrable (d : ℕ) (m : ℝ) (hm : 0 < m) :
    Integrable (Function.uncurry fun (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) =>
      Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
  have hmeas : AEStronglyMeasurable
      (Function.uncurry fun (t : ℝ) (x : EuclideanSpace ℝ (Fin d)) =>
        Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖)
      ((volume.restrict (Set.Ioi 0)).prod volume) := by
    apply Measurable.aestronglyMeasurable
    unfold Function.uncurry heatKernelProfile
    fun_prop
  rw [integrable_prod_iff hmeas]
  refine ⟨?_, ?_⟩
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Function.uncurry_apply_pair]
    exact (heatKernelProfile_integrable d t ht).const_mul _
  · have hint : Integrable (fun t => Real.exp (-t * m ^ 2)) (volume.restrict (Set.Ioi 0)) := by
      have h : (-(m ^ 2) : ℝ) < 0 := neg_neg_of_pos (by positivity)
      have hi := integrableOn_exp_mul_Ioi h 0
      exact hi.congr_fun (fun t _ => by congr 1; ring) measurableSet_Ioi
    refine hint.congr ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Function.uncurry_apply_pair]
    have hnn : ∀ x : EuclideanSpace ℝ (Fin d),
        ‖Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖‖
          = Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖ :=
      fun x => Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (heatKernelProfile_nonneg d t _ ht))
    simp_rw [hnn]
    rw [MeasureTheory.integral_const_mul, heatKernelProfile_integral_eq_one d t ht, mul_one]

/-- The proper-time covariance `x ↦ C_S(‖x‖)` is integrable (`∈ L¹`). -/
lemma properTimeCovariance_integrable (d : ℕ) (m : ℝ) (hm : 0 < m) :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => properTimeCovariance d m ‖x‖) := by
  have h := (schwinger_prod_integrable d m hm).swap.integral_prod_left
  refine h.congr ?_
  filter_upwards with x
  unfold properTimeCovariance
  simp only [Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]

/-- `(4πt)^{-d/2} · e^{-tm²/2} · e^{-1/(8t)}` is integrable on `(0, ∞)`. -/
lemma decayDominator_integrableOn (d : ℕ) (m : ℝ) (hm : 0 < m) :
    IntegrableOn (fun t => (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
      Real.exp (-(m ^ 2 / 2) * t) * Real.exp (-(1 / (8 * t)))) (Set.Ioi 0) := by
  have hb : (0 : ℝ) < m ^ 2 / 2 := by positivity
  have hgi : IntegrableOn (fun t => t ^ ((d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t)) (Set.Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (d : ℝ) / 2) (p := 1) (b := m ^ 2 / 2)
      (by have h2 : (0 : ℝ) ≤ (d : ℝ) / 2 := (by positivity); linarith) (by norm_num) hb
    simpa [Real.rpow_one] using this
  refine (hgi.const_mul ((4 * Real.pi) ^ (-(d : ℝ) / 2) * ((d.factorial : ℝ) * 8 ^ d))).mono' ?_ ?_
  · exact (by fun_prop : Measurable _).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.norm_of_nonneg (by positivity)]
    have hexp : Real.exp (-(1 / (8 * t))) ≤ (d.factorial : ℝ) * 8 ^ d * t ^ d := by
      have hx : (0 : ℝ) ≤ 1 / (8 * t) := by positivity
      have h := Real.pow_div_factorial_le_exp (1 / (8 * t)) hx d
      have hlow : (0 : ℝ) < (1 / (8 * t)) ^ d / d.factorial := by positivity
      rw [Real.exp_neg]
      calc (Real.exp (1 / (8 * t)))⁻¹ ≤ ((1 / (8 * t)) ^ d / d.factorial)⁻¹ := inv_anti₀ hlow h
        _ = (d.factorial : ℝ) * 8 ^ d * t ^ d := by
            rw [inv_div, one_div, inv_pow, div_eq_mul_inv, inv_inv, mul_pow]; ring
    have hkey : t ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (8 * t)))
        ≤ ((d.factorial : ℝ) * 8 ^ d) * t ^ ((d : ℝ) / 2) := by
      have htd : t ^ (-(d : ℝ) / 2) * (t : ℝ) ^ d = t ^ ((d : ℝ) / 2) := by
        rw [← Real.rpow_natCast t d, ← Real.rpow_add ht0]; ring_nf
      calc t ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (8 * t)))
          ≤ t ^ (-(d : ℝ) / 2) * ((d.factorial : ℝ) * 8 ^ d * t ^ d) :=
            mul_le_mul_of_nonneg_left hexp (Real.rpow_nonneg (le_of_lt ht0) _)
        _ = ((d.factorial : ℝ) * 8 ^ d) * t ^ ((d : ℝ) / 2) := by rw [← htd]; ring
    rw [Real.mul_rpow (by positivity) (le_of_lt ht0)]
    calc (4 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t) *
            Real.exp (-(1 / (8 * t)))
        = (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t) *
            (t ^ (-(d : ℝ) / 2) * Real.exp (-(1 / (8 * t)))) := by ring
      _ ≤ (4 * Real.pi) ^ (-(d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t) *
            (((d.factorial : ℝ) * 8 ^ d) * t ^ ((d : ℝ) / 2)) :=
            mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = (4 * Real.pi) ^ (-(d : ℝ) / 2) * ((d.factorial : ℝ) * 8 ^ d) *
            (t ^ ((d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t)) := by ring

/-- Pointwise exponential decay of the proper-time covariance: there is `A ≥ 0` with
    `C_S(r) ≤ A · e^{-(m/2)r}` for all `r ≥ 1` (decay rate `m/2`). -/
lemma properTimeCovariance_decay (d : ℕ) (m : ℝ) (hm : 0 < m) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ r : ℝ, 1 ≤ r →
      properTimeCovariance d m r ≤ A * Real.exp (-(m / 2) * r) := by
  set g : ℝ → ℝ := fun t => (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
    Real.exp (-(m ^ 2 / 2) * t) * Real.exp (-(1 / (8 * t))) with hg
  have hgint : IntegrableOn g (Set.Ioi 0) := decayDominator_integrableOn d m hm
  have hgnn : ∀ t ∈ Set.Ioi (0 : ℝ), 0 ≤ g t := fun t ht => by
    have ht0 : (0 : ℝ) < t := ht
    rw [hg]; dsimp only
    exact mul_nonneg (mul_nonneg
      (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ht0.le) _)
      (Real.exp_nonneg _)) (Real.exp_nonneg _)
  refine ⟨∫ t in Set.Ioi 0, g t, setIntegral_nonneg measurableSet_Ioi hgnn, fun r hr => ?_⟩
  unfold properTimeCovariance
  rw [show (∫ t in Set.Ioi 0, g t) * Real.exp (-(m / 2) * r)
        = ∫ t in Set.Ioi 0, g t * Real.exp (-(m / 2) * r) from (integral_mul_const _ _).symm]
  apply integral_mono_of_nonneg
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.exp_nonneg _) (heatKernelProfile_nonneg d t r ht)
  · exact hgint.mul_const _
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    have hexp_ineq : (m / 2) * r + (m ^ 2 / 2) * t + 1 / (8 * t) ≤ t * m ^ 2 + r ^ 2 / (4 * t) := by
      rw [← sub_nonneg]
      have hkey : t * m ^ 2 + r ^ 2 / (4 * t) - ((m / 2) * r + (m ^ 2 / 2) * t + 1 / (8 * t))
           = ((2 * t * m - r) ^ 2 + (r ^ 2 - 1)) / (8 * t) := by field_simp; ring
      rw [hkey]; apply div_nonneg _ (by positivity)
      nlinarith [sq_nonneg (2 * t * m - r), hr, sq_nonneg (r - 1)]
    have hle : Real.exp (-t * m ^ 2) * Real.exp (-r ^ 2 / (4 * t))
        ≤ Real.exp (-(m ^ 2 / 2) * t) * Real.exp (-(1 / (8 * t))) * Real.exp (-(m / 2) * r) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by simp only [neg_div]; linarith [hexp_ineq])
    rw [hg]
    unfold heatKernelProfile
    calc Real.exp (-t * m ^ 2) * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t)))
        = (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * (Real.exp (-t * m ^ 2) * Real.exp (-r ^ 2 / (4 * t))) := by
          ring
      _ ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
            (Real.exp (-(m ^ 2 / 2) * t) * Real.exp (-(1 / (8 * t))) * Real.exp (-(m / 2) * r)) :=
            mul_le_mul_of_nonneg_left hle
              (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ht0.le) _)
      _ = (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(m ^ 2 / 2) * t) * Real.exp (-(1 / (8 * t))) *
            Real.exp (-(m / 2) * r) := by ring

/-- Joint integrability, over `volume × volume|_{(0,∞)}`, of the Fourier–Schwinger integrand
    `(x, t) ↦ 𝐞(-⟪x, k⟫) · e^{-t m²} H_d(t, ‖x‖)` (character coerced to `ℂ`). -/
lemma schwinger_fourier_prod_integrable (d : ℕ) (m : ℝ) (hm : 0 < m)
    (k : EuclideanSpace ℝ (Fin d)) :
    Integrable (Function.uncurry fun (x : EuclideanSpace ℝ (Fin d)) (t : ℝ) =>
        (Real.fourierChar (-⟪x, k⟫) : ℂ) *
          ((Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖ : ℝ) : ℂ))
      (volume.prod (volume.restrict (Set.Ioi 0))) := by
  have h_ae_pos : ∀ᵐ p : EuclideanSpace ℝ (Fin d) × ℝ
      ∂((volume : Measure (EuclideanSpace ℝ (Fin d))).prod (volume.restrict (Set.Ioi 0))),
      0 < p.2 := by
    have hprod : (volume : Measure (EuclideanSpace ℝ (Fin d))).prod
          ((volume : Measure ℝ).restrict (Set.Ioi 0))
        = ((volume : Measure (EuclideanSpace ℝ (Fin d))).prod volume).restrict
            (Set.univ ×ˢ Set.Ioi 0) := by
      rw [← MeasureTheory.Measure.prod_restrict, MeasureTheory.Measure.restrict_univ]
    rw [hprod]
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioi)] with p hp
    exact hp.2
  refine ((schwinger_prod_integrable d m hm).swap).mono' ?_ ?_
  · have hchar : Continuous fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
        (Real.fourierChar (-⟪p.1, k⟫) : ℂ) :=
      continuous_subtype_val.comp
        (Real.continuous_fourierChar.comp (continuous_fst.inner continuous_const).neg)
    have hker : Measurable fun p : EuclideanSpace ℝ (Fin d) × ℝ =>
        ((Real.exp (-p.2 * m ^ 2) * heatKernelProfile d p.2 ‖p.1‖ : ℝ) : ℂ) := by
      unfold heatKernelProfile
      fun_prop
    exact (hchar.measurable.mul hker).aestronglyMeasurable
  · filter_upwards [h_ae_pos] with p hp
    obtain ⟨x, t⟩ := p
    have hnn : 0 ≤ Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖ :=
      mul_nonneg (Real.exp_nonneg _) (heatKernelProfile_nonneg d t _ hp)
    simp only [Function.comp_apply, Prod.swap_prod_mk, Function.uncurry_apply_pair]
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real]
    exact le_of_eq (Real.norm_of_nonneg hnn)

/-- The forward Fourier transform of the proper-time covariance `x ↦ C_S(‖x‖)` is the momentum
    propagator: `𝓕[C_S(‖·‖)](k) = 1/((2π)²‖k‖² + m²)`, uniformly in `d` (Fubini over the
    proper-time integral, the heat-kernel Fourier transform, and the Laplace integral in `t`). -/
lemma properTimeCovariance_fourier (d : ℕ) (m : ℝ) (hm : 0 < m) (k : EuclideanSpace ℝ (Fin d)) :
    FourierTransform.fourier
        (fun x : EuclideanSpace ℝ (Fin d) => (properTimeCovariance d m ‖x‖ : ℂ)) k
      = (freePropagatorMom d m k : ℂ) := by
  have hCS : ∀ (c : ℂ) (x : EuclideanSpace ℝ (Fin d)),
      c * ((properTimeCovariance d m ‖x‖ : ℝ) : ℂ)
        = ∫ t in Set.Ioi 0,
            c * ((Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖ : ℝ) : ℂ) := by
    intro c x
    have h1 : ((properTimeCovariance d m ‖x‖ : ℝ) : ℂ)
        = ∫ t in Set.Ioi 0, ((Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖ : ℝ) : ℂ) := by
      unfold properTimeCovariance
      rw [integral_complex_ofReal]
    rw [h1]
    exact (MeasureTheory.integral_const_mul _ _).symm
  have hinner : ∀ t ∈ Set.Ioi (0 : ℝ),
      (∫ x : EuclideanSpace ℝ (Fin d),
          (Real.fourierChar (-⟪x, k⟫) : ℂ) *
            ((Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖ : ℝ) : ℂ))
        = ((Real.exp (-(m ^ 2 + (2 * Real.pi) ^ 2 * ‖k‖ ^ 2) * t) : ℝ) : ℂ) := by
    intro t ht
    have hFT := heatKernelProfile_fourier d t ht k
    rw [Real.fourier_eq] at hFT
    simp_rw [Circle.smul_def, smul_eq_mul] at hFT
    calc (∫ x : EuclideanSpace ℝ (Fin d),
            (Real.fourierChar (-⟪x, k⟫) : ℂ) *
              ((Real.exp (-t * m ^ 2) * heatKernelProfile d t ‖x‖ : ℝ) : ℂ))
        = ∫ x : EuclideanSpace ℝ (Fin d),
            ((Real.exp (-t * m ^ 2) : ℝ) : ℂ) *
              ((Real.fourierChar (-⟪x, k⟫) : ℂ) * ((heatKernelProfile d t ‖x‖ : ℝ) : ℂ)) :=
          MeasureTheory.integral_congr_ae
            (Filter.Eventually.of_forall fun x => by push_cast; ring)
      _ = ((Real.exp (-t * m ^ 2) : ℝ) : ℂ) *
            ∫ x : EuclideanSpace ℝ (Fin d),
              (Real.fourierChar (-⟪x, k⟫) : ℂ) * ((heatKernelProfile d t ‖x‖ : ℝ) : ℂ) :=
          MeasureTheory.integral_const_mul _ _
      _ = ((Real.exp (-t * m ^ 2) : ℝ) : ℂ) *
            Complex.exp (-(4 * Real.pi ^ 2 * t : ℝ) * ‖k‖ ^ 2) :=
          congrArg (fun z => ((Real.exp (-t * m ^ 2) : ℝ) : ℂ) * z) hFT
      _ = ((Real.exp (-(m ^ 2 + (2 * Real.pi) ^ 2 * ‖k‖ ^ 2) * t) : ℝ) : ℂ) := by
          rw [Complex.ofReal_exp, Complex.ofReal_exp, ← Complex.exp_add]
          congr 1
          push_cast
          ring
  have hA : (0 : ℝ) < m ^ 2 + (2 * Real.pi) ^ 2 * ‖k‖ ^ 2 := by positivity
  have hlaplace : ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-(m ^ 2 + (2 * Real.pi) ^ 2 * ‖k‖ ^ 2) * t) = freePropagatorMom d m k := by
    rw [integral_exp_mul_Ioi (by linarith) 0, mul_zero, Real.exp_zero, neg_div_neg_eq]
    unfold freePropagatorMom
    rw [add_comm]
  rw [Real.fourier_eq]
  simp_rw [Circle.smul_def, smul_eq_mul, hCS]
  exact (MeasureTheory.integral_integral_swap (schwinger_fourier_prod_integrable d m hm k)).trans
    ((MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hinner).trans
      (integral_complex_ofReal.trans (congrArg Complex.ofReal hlaplace)))

/-- The dimension-generic free-propagator typeclass.

    Two obligations only: the per-`d` closed-form radial covariance `Cprofile`, and the single
    bridge `schwinger_eq` identifying it (for `r > 0`; the covariance has an integrable singularity
    at `r = 0`) with the generic proper-time integral `properTimeCovariance`. Its `L¹`-integrability
    (`GFFPropagator.integrable`), Fourier transform (`GFFPropagator.fourier_eq`), and exponential
    decay (`GFFPropagator.decayBound`) then hold for every `d`. `[Fact (2 ≤ d)]` supports the
    time/space split. -/
class GFFPropagator (d : ℕ) (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)] where
  /-- The per-`d` radial profile of the position-space covariance: `C(x, y) = Cprofile ‖x − y‖`. -/
  Cprofile : ℝ → ℝ
  /-- `Cprofile` equals the generic proper-time integral for `r > 0`. The genuine per-`d` obligation
      (evaluate the proper-time integral to the closed form). -/
  schwinger_eq : ∀ r > 0, Cprofile r = properTimeCovariance d m r

/-- The canonical propagator in any dimension `2 ≤ d`, taking `Cprofile` to be the generic
    proper-time covariance itself (so `schwinger_eq` is `rfl`). It discharges `GFFPropagator d m`
    for every `d` with no closed form required, hence witnesses that the master theorem holds in
    every dimension `d ≥ 2`. This is a `def`, deliberately not a global `instance`: the class
    carries data, and a competing global instance would make the constructed measure differ from
    the concrete per-`d` instances'. -/
@[reducible] def GFFPropagator.ofProperTime (d : ℕ) (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)] :
    GFFPropagator d m where
  Cprofile := properTimeCovariance d m
  schwinger_eq _ _ := rfl

namespace GFFPropagator

variable {d : ℕ} {m : ℝ} [Fact (0 < m)] [Fact (2 ≤ d)] [GFFPropagator d m]

/-- `x ↦ Cprofile ‖x‖` is integrable (`∈ L¹`); the local-integrability input for OS1. -/
lemma integrable :
    Integrable (fun x : EuclideanSpace ℝ (Fin d) => Cprofile (d := d) (m := m) ‖x‖) := by
  have hm : (0 : ℝ) < m := Fact.out
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance
  refine (properTimeCovariance_integrable d m hm).congr ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : EuclideanSpace ℝ (Fin d)))] with x hx
  exact (schwinger_eq ‖x‖ (norm_pos_iff.mpr (by simpa using hx))).symm

/-- `Cprofile` has pointwise exponential decay: for some `A ≥ 0`,
    `|Cprofile r| ≤ A · e^{-(m/2)r}` whenever `1 ≤ r`; the decay input for OS4 clustering. -/
lemma decayBound : ∃ A : ℝ, 0 ≤ A ∧
    ∀ r : ℝ, 1 ≤ r → |Cprofile (d := d) (m := m) r| ≤ A * Real.exp (-(m / 2) * r) := by
  obtain ⟨A, hA, hbound⟩ := properTimeCovariance_decay d m Fact.out
  refine ⟨A, hA, fun r hr => ?_⟩
  have hr0 : (0 : ℝ) < r := lt_of_lt_of_le one_pos hr
  rw [schwinger_eq r hr0, abs_of_nonneg (properTimeCovariance_nonneg d m r)]
  exact hbound r hr

/-- The forward Fourier transform of `x ↦ Cprofile ‖x‖` is the momentum-space propagator
    `k ↦ 1/((2π)²‖k‖² + m²)`; the momentum-space input for the Parseval/OS1/OS3 chain. -/
lemma fourier_eq :
    FourierTransform.fourier
        (fun x : EuclideanSpace ℝ (Fin d) => (Cprofile (d := d) (m := m) ‖x‖ : ℂ))
      = fun k => (freePropagatorMom d m k : ℂ) := by
  have hm : (0 : ℝ) < m := Fact.out
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (EuclideanSpace ℝ (Fin d)) := inferInstance
  have hae : (fun x : EuclideanSpace ℝ (Fin d) => (Cprofile (d := d) (m := m) ‖x‖ : ℂ))
      =ᵐ[volume] fun x => (properTimeCovariance d m ‖x‖ : ℂ) := by
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : EuclideanSpace ℝ (Fin d)))]
      with x hx
    rw [schwinger_eq (d := d) (m := m) ‖x‖ (norm_pos_iff.mpr (by simpa using hx))]
  funext k
  exact (Real.fourier_congr_ae hae k).trans (properTimeCovariance_fourier d m hm k)

end GFFPropagator

end

end OSforGFF

noncomputable section

open OSforGFF

/-- The position-space free covariance kernel: `C(x, y) = Cprofile ‖x - y‖`, radial in the
    separation. The per-`d` closed form enters only through `GFFPropagator.Cprofile`. -/
def freeCovariance (d : ℕ) (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)] [GFFPropagator d m]
    (x y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  GFFPropagator.Cprofile (d := d) (m := m) ‖x - y‖

variable {d : ℕ} {m : ℝ} [Fact (0 < m)] [Fact (2 ≤ d)] [GFFPropagator d m]

/-- The covariance kernel is symmetric: `C(x, y) = C(y, x)`. -/
lemma freeCovariance_symm (x y : EuclideanSpace ℝ (Fin d)) :
    freeCovariance d m x y = freeCovariance d m y x := by
  unfold freeCovariance
  rw [norm_sub_rev]

end
