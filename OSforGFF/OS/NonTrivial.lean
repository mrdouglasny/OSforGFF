/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import OSforGFF.Measure.Construct
import OSforGFF.Covariance.RealForm
import OSforGFF.Spacetime.ComplexTestFunction
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Nontriviality of the Gaussian Free Field

The OS axiom verification in `OS.Master` would be trivially satisfied by the Dirac
measure at ω = 0 (the "zero field").  This file closes that loophole by proving
the GFF measure is **strictly non-degenerate**:

1. The square-root propagator embedding `T : S(ℝ^d) → L²` is injective.
2. The smeared covariance `C(f,f) > 0` for every nonzero test function `f`.
3. Every field pairing `⟨ω,f⟩` has strictly positive variance under the free GFF.
4. The pointwise kernel `C(x,y) → +∞` as `x → y` (UV divergence), for every dimension
   `d ≥ 2`: the radial profile is the proper-time integral `properTimeCovariance d m r`,
   whose `t^{-d/2}` short-time singularity forces at least logarithmic blow-up as `r → 0⁺`
   (the sharp rate is `log(1/r)` at `d = 2` and `r^{2−d}` for `d ≥ 3`).

## Proof strategy

Injectivity of T follows from:
- Fourier transform is injective on Schwartz space (Mathlib's `FourierPair` instance
  gives a left inverse `𝓕⁻ ∘ 𝓕 = id`).
- The momentum-space weight `1/√(‖k‖² + m²)` is everywhere positive, so
  multiplication by it cannot create new zeros.
- A continuous function that vanishes a.e. with respect to Lebesgue measure
  vanishes everywhere (volume is an `IsOpenPosMeasure`).

## Main results

- `toComplex_injective` : embedding `S(ℝ^d,ℝ) ↪ S(ℝ^d,ℂ)` is injective
- `fourierTransform_schwartz_injective` : `𝓕` on Schwartz space is injective
- `embeddingMap_injective` : the square-root propagator embedding is injective
- `freeCovarianceFormR_strictPos` : `C(f,f) > 0` for `f ≠ 0`
- `gaussianFreeField_variance_pos` : `Var[⟨ω,f⟩] > 0` for `f ≠ 0`
- `gaussianFreeField_not_dirac` : `μ_GFF ≠ δ₀`
- `properTimeCovariance_tendsto_atTop_at_zero` : `properTimeCovariance d m r → +∞` as `r → 0⁺` (`d ≥ 2`)
- `freeCovariance_tendsto_atTop` : `C(x,y) → +∞` as `x → y` (generic in `d ≥ 2`)

## References

- Glimm–Jaffe, *Quantum Physics*, §6.1 (nondegeneracy of the free field)
- Reed–Simon, *Methods of Modern Mathematical Physics* II, §IX.8

## Build status

This file is deliberately **off the root import graph** — the headline theorems of
`OS.Master` do not depend on it, and `lake build` does not compile it. It is verified
separately, via `lake env lean`, by `scripts/check-guardrails.sh`.
-/

open MeasureTheory Complex QFT
open scoped Real BigOperators SchwartzMap

noncomputable section

variable {d : ℕ} [Fact (2 ≤ d)]

namespace OSforGFF

/-! ## Injectivity of the real-to-complex embedding -/

omit [Fact (2 ≤ d)] in
/-- The embedding `toComplex : S(ℝ^d,ℝ) → S(ℝ^d,ℂ)` is injective.
    Follows from injectivity of `ℝ → ℂ` applied pointwise. -/
theorem toComplex_injective : Function.Injective (toComplex : SchwartzTestFunction d → SchwartzTestFunctionℂ d) := by
  intro f g h
  ext x
  have : toComplex f x = toComplex g x := congr_fun (congr_arg _ h) x
  simp only [toComplex_apply, Complex.ofReal_inj] at this
  exact this

/-! ## Injectivity of the Fourier transform on Schwartz space -/

omit [Fact (2 ≤ d)] in
/-- The Fourier transform is injective on complex Schwartz space.
    Proof: `FourierPair` gives `𝓕⁻(𝓕 f) = f`, so `𝓕` has a left inverse. -/
theorem fourierTransform_schwartz_injective :
    Function.Injective
      (SchwartzMap.fourierTransformCLM ℂ : SchwartzTestFunctionℂ d → SchwartzTestFunctionℂ d) := by
  intro f g h
  -- SchwartzMap.fourierTransformCLM agrees with FourierTransform.fourier
  have hf' : (SchwartzMap.fourierTransformCLM ℂ f : SchwartzTestFunctionℂ d) =
    FourierTransform.fourier f := rfl
  have hg' : (SchwartzMap.fourierTransformCLM ℂ g : SchwartzTestFunctionℂ d) =
    FourierTransform.fourier g := rfl
  rw [hf', hg'] at h
  -- FourierPair gives 𝓕⁻ ∘ 𝓕 = id on Schwartz space
  calc f = FourierTransform.fourierInv (FourierTransform.fourier f) :=
        (FourierTransform.fourierInv_fourier_eq f).symm
    _ = FourierTransform.fourierInv (FourierTransform.fourier g) := by rw [h]
    _ = g := FourierTransform.fourierInv_fourier_eq g

/-! ## Continuous functions that vanish a.e. vanish everywhere -/

omit [Fact (2 ≤ d)] in
/-- A continuous function `SpaceTime d → ℂ` that is zero a.e. with respect to
    Lebesgue measure is zero everywhere.

    Proof: if `f(x₀) ≠ 0`, then `U = f⁻¹(ℂ \ {0})` is open and nonempty.
    Since volume on `ℝ^d` is an `IsOpenPosMeasure`, `μ(U) > 0`,
    contradicting `f = 0` a.e. -/
private lemma eq_zero_of_continuous_ae_zero
    {f : SpaceTime d → ℂ} (hcont : Continuous f) (hae : f =ᵐ[volume] 0) :
    f = 0 := by
  funext x
  by_contra hx
  have hU_open : IsOpen {y : SpaceTime d | f y ≠ 0} :=
    hcont.isOpen_preimage _ isOpen_compl_singleton
  have hU_ne : Set.Nonempty {y : SpaceTime d | f y ≠ 0} := ⟨x, hx⟩
  have hU_pos : 0 < volume {y : SpaceTime d | f y ≠ 0} :=
    hU_open.measure_pos volume hU_ne
  have hU_zero : volume {y : SpaceTime d | f y ≠ 0} = 0 := by
    rw [← ae_iff]
    exact hae.mono fun y hy => by simpa using hy
  exact absurd hU_zero (ne_of_gt hU_pos)

/-! ## Injectivity of the square-root propagator embedding -/

/-- The square-root propagator map is zero pointwise only if f = 0.

    `sqrtPropagatorMap m f k = 𝓕(toComplex f)(k) · w(k)` where `w(k) > 0`,
    so vanishing of the product forces `𝓕(toComplex f) = 0`, hence `f = 0`
    by Fourier injectivity. -/
theorem sqrtPropagatorMap_eq_zero_iff (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : SchwartzTestFunction d) :
    (∀ k : SpaceTime d, sqrtPropagatorMap m f k = 0) ↔ f = 0 := by
  constructor
  · intro h
    -- Each factor: 𝓕(toComplex f)(k) * w(k) = 0, and w(k) > 0, so 𝓕(toComplex f)(k) = 0
    have h_ft_zero : ∀ k, (SchwartzMap.fourierTransformCLM ℂ (toComplex f)) k = 0 := by
      intro k
      have := h k
      unfold sqrtPropagatorMap at this
      have hw_pos : (freePropagatorMomSqrt d m k : ℂ) ≠ 0 := by
        simp only [Complex.ofReal_ne_zero]
        exact ne_of_gt (freePropagatorMomSqrt_pos m k)
      exact (mul_eq_zero.mp this).resolve_right hw_pos
    -- 𝓕(toComplex f) = 0 as a Schwartz function
    have h_ft_zero_fn : SchwartzMap.fourierTransformCLM ℂ (toComplex f) = 0 := by
      ext k; exact h_ft_zero k
    -- By Fourier injectivity, toComplex f = 0
    have h_tc_zero : toComplex f = 0 := by
      have : SchwartzMap.fourierTransformCLM ℂ (toComplex f) =
             SchwartzMap.fourierTransformCLM ℂ 0 := by
        rw [h_ft_zero_fn, map_zero]
      exact fourierTransform_schwartz_injective this
    -- By toComplex injectivity, f = 0
    have h_tc_0 : toComplex (0 : SchwartzTestFunction d) = 0 := by ext x; simp [toComplex_apply]
    exact toComplex_injective (h_tc_zero.trans h_tc_0.symm)
  · intro h; subst h; intro k
    unfold sqrtPropagatorMap
    have h1 : toComplex (0 : SchwartzTestFunction d) = 0 := by ext x; simp [toComplex_apply]
    rw [h1]
    have h2 : SchwartzMap.fourierTransformCLM ℂ (0 : SchwartzTestFunctionℂ d) = 0 :=
      ContinuousLinearMap.map_zero _
    simp only [h2, zero_apply, zero_mul]

/-- The embedding `T : S(ℝ^d,ℝ) → L²(ℝ^d,ℂ)` is injective.

    If `T f = T g` then `‖T(f−g)‖ = 0`, so `∫ |sqrtPropagatorMap m (f−g)|² = 0`.
    The integrand is continuous and nonneg, so it vanishes a.e., hence everywhere
    (volume is `IsOpenPosMeasure`).  Since the momentum weight is positive, the
    Fourier transform of `f−g` vanishes, giving `f = g`. -/
theorem embeddingMap_injective (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    Function.Injective (embeddingMap (d := d) m) := by
  intro f g h
  suffices f - g = 0 from eq_of_sub_eq_zero this
  -- T(f-g) = 0 in L²
  have h_zero : embeddingMap m (f - g) = 0 := by
    rw [map_sub, h, sub_self]
  -- ‖T(f-g)‖² = ∫ |sqrtPropagatorMap|² = 0
  have h_norm_zero : ‖embeddingMap m (f - g)‖ = 0 := by rw [h_zero, norm_zero]
  have h_int_zero : ∫ k, ‖sqrtPropagatorMap m (f - g) k‖ ^ 2 ∂volume = 0 := by
    have := embeddingMap_norm_sq m (f - g)
    rw [h_norm_zero, zero_pow (by norm_num : 2 ≠ 0)] at this
    linarith
  -- Nonneg continuous integrand with zero integral vanishes a.e.
  have h_int := sqrtPropagatorMap_sq_integrable (m := m) (f := f - g)
  have h_ae_zero : ∀ᵐ k ∂volume, ‖sqrtPropagatorMap m (f - g) k‖ ^ 2 = 0 := by
    exact (integral_eq_zero_iff_of_nonneg_ae
      (Filter.Eventually.of_forall fun k => sq_nonneg _) h_int).mp h_int_zero
  -- ‖·‖² = 0 implies · = 0
  have h_ae_zero' : ∀ᵐ k ∂volume, sqrtPropagatorMap m (f - g) k = 0 :=
    h_ae_zero.mono fun k hk => by rwa [sq_eq_zero_iff, norm_eq_zero] at hk
  -- Continuous function zero a.e. is zero everywhere
  have h_cont : Continuous (fun k => sqrtPropagatorMap m (f - g) k) := by
    unfold sqrtPropagatorMap
    exact ((SchwartzMap.fourierTransformCLM ℂ (toComplex (f - g))).continuous).mul
      (continuous_ofReal.comp (freePropagatorMomSqrt_continuous m))
  have h_ptwise : ∀ k, sqrtPropagatorMap m (f - g) k = 0 := by
    have h_eq := eq_zero_of_continuous_ae_zero h_cont
      (h_ae_zero'.mono fun k hk => by simp [hk])
    exact fun k => congr_fun h_eq k
  exact (sqrtPropagatorMap_eq_zero_iff m (f - g)).mp h_ptwise

/-! ## Strict positivity of the covariance -/

/-- **Strict positive definiteness**: the smeared covariance `C(f,f) > 0` for any
    nonzero test function `f`.  This rules out the Dirac-at-zero measure as
    a model satisfying the OS axioms.

    Proof: `C(f,f) = ‖T f‖²` where `T` is injective, so `f ≠ 0 ⟹ T f ≠ 0
    ⟹ ‖T f‖ > 0 ⟹ ‖T f‖² > 0`. -/
theorem freeCovarianceFormR_strictPos (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (f : SchwartzTestFunction d) (hf : f ≠ 0) :
    0 < freeCovarianceFormR m f f := by
  rw [freeCovarianceFormR_eq_normSq m f]
  have h_ne : embeddingMap m f ≠ 0 := by
    intro h_abs
    exact hf (embeddingMap_injective m (h_abs.trans (map_zero (embeddingMap m)).symm))
  exact sq_pos_of_pos (norm_pos_iff.mpr h_ne)

/-! ## Nontriviality of the GFF measure -/

/-- The variance of `⟨ω,f⟩` under the GFF is strictly positive for `f ≠ 0`.
    Equivalently, the pushforward by the pairing is a non-degenerate Gaussian. -/
theorem gaussianFreeField_variance_pos (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (f : SchwartzTestFunction d) (hf : f ≠ 0) :
    0 < ∫ ω, (distributionPairingCLM f ω) ^ 2 ∂(gaussianFreeField_free (d := d) m).toMeasure := by
  rw [gff_second_moment_eq_covariance]
  exact freeCovarianceFormR_strictPos m f hf

/-- **The GFF is not a Dirac measure**: there exists a test function whose pairing
    with ω has nonzero variance.  This is the formal statement that the OS axiom
    verification in `Master.lean` is nontrivial.

    Any nonzero Schwartz function witnesses this.  We use a standard bump
    function on ℝ^d, which exists by `ContDiff.exists_eq_one_of_isOpen`. -/
theorem gaussianFreeField_not_dirac (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    ∃ f : SchwartzTestFunction d, f ≠ 0 ∧
      0 < ∫ ω, (distributionPairingCLM f ω) ^ 2 ∂(gaussianFreeField_free (d := d) m).toMeasure := by
  -- Schwartz space on ℝ^d is nontrivial: exhibit a nonzero element.
  -- This uses the existence of smooth compactly-supported bump functions.
  have ⟨f, hf⟩ : ∃ f : SchwartzTestFunction d, f ≠ 0 := by
    let φ : ContDiffBump (0 : SpaceTime d) := ⟨1, 2, by norm_num, by norm_num⟩
    refine ⟨φ.hasCompactSupport.toSchwartzMap φ.contDiff, fun h => ?_⟩
    have h1 : φ (0 : SpaceTime d) = 1 :=
      φ.one_of_mem_closedBall (Metric.mem_closedBall_self φ.rIn_pos.le)
    have h2 : (φ.hasCompactSupport.toSchwartzMap φ.contDiff) (0 : SpaceTime d) =
              φ (0 : SpaceTime d) := rfl
    rw [h] at h2; simp at h2; linarith
  exact ⟨f, hf, gaussianFreeField_variance_pos m f hf⟩

/-! ## UV divergence: pointwise covariance diverges at coincident points

The pointwise regularization `C(x,x) = 0` at coincident points is a convention for the smeared
(distribution) theory.  The actual limit diverges, confirming that the free field has genuine UV
singularity: the radial profile is the proper-time integral `properTimeCovariance d m r`, whose
`t^{−d/2}` short-time singularity forces blow-up as `r → 0⁺` for every `d ≥ 2`.

The smeared covariance `C(f,f) = ∫∫ f(x) C(x,y) f(y) dx dy` remains finite for all Schwartz
functions because the position-space kernel is `L¹` (`GFFPropagator.integrable`): the short-distance
singularity `∼ ‖x−y‖^{−(d−2)}` is integrable in `d` dimensions (the `d`-dimensional volume element
`∼ r^{d−1}` compensates the kernel), so no separate radial estimate is needed. -/

omit [Fact (2 ≤ d)] in
/-- For `d ≥ 2` the proper-time covariance diverges at the origin:
    `properTimeCovariance d m r → +∞` as `r → 0⁺`. Lower bound: on the window `[r², (4π)⁻¹]`
    the integrand dominates a constant multiple of `1/t`, so the integral grows at least like
    `log(1/r²)` — the sharp rate at `d = 2`; for `d ≥ 3` the true rate `r^{2−d}` is polynomial. -/
theorem properTimeCovariance_tendsto_atTop_at_zero (m : ℝ) (hm : 0 < m) (hd : 2 ≤ d) :
    Filter.Tendsto (fun r => properTimeCovariance d m r)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
  have hinv : (0 : ℝ) < (4 * Real.pi)⁻¹ := by positivity
  set c₀ : ℝ := Real.exp (-m ^ 2 * (4 * Real.pi)⁻¹) * ((4 * Real.pi)⁻¹ * Real.exp (-(1 / 4 : ℝ)))
    with hc₀
  have hc₀_pos : (0 : ℝ) < c₀ := by rw [hc₀]; positivity
  set L : ℝ → ℝ := fun r => c₀ * (Real.log ((4 * Real.pi)⁻¹) - Real.log (r ^ 2)) with hL
  have hL_le : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), L r ≤ properTimeCovariance d m r := by
    have hcond : ∀ᶠ r in nhdsWithin (0 : ℝ) (Set.Ioi 0), r ^ 2 ≤ (4 * Real.pi)⁻¹ := by
      have hcont : Filter.Tendsto (fun r : ℝ => r ^ 2) (nhds 0) (nhds 0) := by
        have h := (by fun_prop : Continuous (fun r : ℝ => r ^ 2)).tendsto 0
        simpa using h
      exact (hcont.eventually (Filter.eventually_of_mem
        (Iic_mem_nhds hinv) fun x hx => hx)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hcond] with r hr hcondr
    have hr0 : (0 : ℝ) < r := hr
    have hr2 : (0 : ℝ) < r ^ 2 := pow_pos hr0 2
    have hInt : MeasureTheory.IntegrableOn
        (fun t => Real.exp (-t * m ^ 2) * heatKernelProfile d t r) (Set.Ioi 0) :=
      properTime_slice_integrableOn d m hm hr0
    -- On the window the integrand dominates `c₀ / t`.
    have hbound : ∀ t ∈ Set.Icc (r ^ 2) ((4 * Real.pi)⁻¹),
        c₀ * t⁻¹ ≤ Real.exp (-t * m ^ 2) * heatKernelProfile d t r := by
      intro t ht
      have ht1 : r ^ 2 ≤ t := ht.1
      have ht2 : t ≤ (4 * Real.pi)⁻¹ := ht.2
      have ht0 : (0 : ℝ) < t := lt_of_lt_of_le hr2 ht1
      simp only [heatKernelProfile]
      have h1 : Real.exp (-m ^ 2 * (4 * Real.pi)⁻¹) ≤ Real.exp (-t * m ^ 2) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_left ht2 (sq_nonneg m)])
      have h2 : (4 * Real.pi)⁻¹ * t⁻¹ ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
        have hbase : (0 : ℝ) < 4 * Real.pi * t := by positivity
        have hb1 : 4 * Real.pi * t ≤ 1 := by
          calc 4 * Real.pi * t ≤ 4 * Real.pi * (4 * Real.pi)⁻¹ :=
                mul_le_mul_of_nonneg_left ht2 (by positivity)
            _ = 1 := mul_inv_cancel₀ (by positivity)
        have hexp_le : -(d : ℝ) / 2 ≤ -1 := by
          have hdR : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
          linarith
        calc (4 * Real.pi)⁻¹ * t⁻¹ = (4 * Real.pi * t)⁻¹ := (mul_inv _ _).symm
          _ = (4 * Real.pi * t) ^ (-1 : ℝ) := (Real.rpow_neg_one _).symm
          _ ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) :=
              Real.rpow_le_rpow_of_exponent_ge hbase hb1 hexp_le
      have h3 : Real.exp (-(1 / 4 : ℝ)) ≤ Real.exp (-r ^ 2 / (4 * t)) := by
        apply Real.exp_le_exp.mpr
        rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity : (0 : ℝ) < 4 * t)]
        nlinarith [ht1]
      calc c₀ * t⁻¹
          = Real.exp (-m ^ 2 * (4 * Real.pi)⁻¹)
              * ((4 * Real.pi)⁻¹ * t⁻¹ * Real.exp (-(1 / 4 : ℝ))) := by rw [hc₀]; ring
        _ ≤ Real.exp (-t * m ^ 2)
              * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-r ^ 2 / (4 * t))) :=
            mul_le_mul h1 (mul_le_mul h2 h3 (by positivity) (by positivity))
              (by positivity) (by positivity)
    have hwin_int : MeasureTheory.IntegrableOn (fun t : ℝ => c₀ * t⁻¹)
        (Set.Icc (r ^ 2) ((4 * Real.pi)⁻¹)) := by
      apply MeasureTheory.Integrable.const_mul
      exact (continuousOn_inv₀.mono fun t ht =>
        ne_of_gt (lt_of_lt_of_le hr2 ht.1)).integrableOn_compact isCompact_Icc
    calc L r
        = ∫ t in Set.Icc (r ^ 2) ((4 * Real.pi)⁻¹), c₀ * t⁻¹ := by
          rw [MeasureTheory.integral_Icc_eq_integral_Ioc,
              ← intervalIntegral.integral_of_le hcondr,
              intervalIntegral.integral_const_mul, integral_inv_of_pos hr2 hinv,
              Real.log_div hinv.ne' hr2.ne', hL]
      _ ≤ ∫ t in Set.Icc (r ^ 2) ((4 * Real.pi)⁻¹),
            Real.exp (-t * m ^ 2) * heatKernelProfile d t r :=
          setIntegral_mono_on hwin_int
            (hInt.mono_set fun t ht => lt_of_lt_of_le hr2 ht.1) measurableSet_Icc hbound
      _ ≤ ∫ t in Set.Ioi 0, Real.exp (-t * m ^ 2) * heatKernelProfile d t r := by
          apply setIntegral_mono_set hInt
          · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
            exact mul_nonneg (Real.exp_nonneg _) (heatKernelProfile_nonneg d t r ht)
          · exact Filter.Eventually.of_forall fun t (ht : t ∈ Set.Icc _ _) =>
              lt_of_lt_of_le hr2 ht.1
      _ = properTimeCovariance d m r := rfl
  have hL_tendsto : Filter.Tendsto L (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
    have hsq : Filter.Tendsto (fun r : ℝ => r ^ 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have h := ((continuous_pow 2).continuousAt (x := (0 : ℝ))).tendsto
        simpa using h.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with r hr
        exact pow_pos (Set.mem_Ioi.mp hr) 2
    have hlog : Filter.Tendsto (fun r : ℝ => Real.log (r ^ 2))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atBot :=
      Real.tendsto_log_nhdsGT_zero.comp hsq
    have hneg : Filter.Tendsto (fun r : ℝ => -Real.log (r ^ 2))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
      Filter.tendsto_neg_atBot_atTop.comp hlog
    have hadd := Filter.tendsto_atTop_add_const_left (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (Real.log ((4 * Real.pi)⁻¹)) hneg
    simp only [hL, sub_eq_add_neg]
    exact Filter.Tendsto.const_mul_atTop hc₀_pos hadd
  exact Filter.tendsto_atTop_mono' _ hL_le hL_tendsto

/-- The free covariance `C(x₀, x) → +∞` as `x → x₀` (UV divergence), for any dimension `d ≥ 2`
    equipped with a `GFFPropagator d m` instance.

    The radial profile `Cprofile r = properTimeCovariance d m r` diverges at `r → 0⁺`
    (`properTimeCovariance_tendsto_atTop_at_zero`); composing with `‖x₀ − x‖ → 0⁺` gives the UV
    blow-up. The covariance kernel is thus unbounded, so the GFF measure is not a point mass.
    Specialising to `d = 4` recovers the Bessel-`K₁` kernel statement, to `d = 3` the Yukawa
    kernel, and to `d = 2` the logarithmically divergent `K₀` kernel. -/
theorem freeCovariance_tendsto_atTop (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (x₀ : SpaceTime d) :
    Filter.Tendsto (fun x => freeCovariance d m x₀ x)
      (nhdsWithin x₀ {x₀}ᶜ) Filter.atTop := by
  have hm : 0 < m := Fact.out
  -- `‖x₀ − x‖ → 0⁺` as `x → x₀` through `{x₀}ᶜ` (dimension-generic).
  have h_norm : Filter.Tendsto (fun x => ‖x₀ - x‖)
      (nhdsWithin x₀ {x₀}ᶜ) (nhdsWithin 0 (Set.Ioi 0)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc : ContinuousAt (fun x : SpaceTime d => ‖x₀ - x‖) x₀ :=
        (continuous_norm.comp (continuous_const.sub continuous_id)).continuousAt
      have := hc.tendsto; simp only [sub_self, norm_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · exact eventually_nhdsWithin_of_forall fun x hx =>
        norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hx (Set.mem_singleton_iff.mpr h.symm))
  refine ((properTimeCovariance_tendsto_atTop_at_zero m hm
    (Fact.out : 2 ≤ d)).comp h_norm).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hpos : 0 < ‖x₀ - x‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr fun h => hx (Set.mem_singleton_iff.mpr h.symm))
  show properTimeCovariance d m ‖x₀ - x‖ = freeCovariance d m x₀ x
  simp only [freeCovariance, GFFPropagator.schwinger_eq ‖x₀ - x‖ hpos]

end OSforGFF
