/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import OSforGFF.General.FunctionalAnalysis
import OSforGFF.Spacetime.Basic
import OSforGFF.Spacetime.ComplexTestFunction
import OSforGFF.Spacetime.DiscreteSymmetry
import OSforGFF.Spacetime.Euclidean
import OSforGFF.Covariance.Propagator

/-!
# The dimension-generic Parseval bridge

Everything the OS proofs need about the covariance pairing of Schwartz test functions,
derived once for every dimension `d` from the two `GFFPropagator` fields. The central
identity is the Parseval bridge for the quadratic pairing,

  `(freeCovarianceℂ m f f).re = ∫ k, ‖𝓕f(k)‖² · P(k) dk`,   `P = freePropagatorMom d m`,

from which positivity of the covariance is immediate: the momentum weight
`P(k) = 1/((2π)²‖k‖² + m²)` is pointwise positive.

**The derivation** never touches the closed-form kernel. Since `C(x,y) = Cprofile ‖x−y‖`
agrees with the proper-time covariance `C_S` away from the (null) diagonal, the pairing may
be computed against `C_S` throughout:

1. *Shear/Fubini.* The change of variables `(x,y) ↦ (x, x−y)` turns the double integral
   into `∫ C_S(‖z‖) · A(z) dz`, where `A(z) = ∫ f(x) conj (f (x−z))` is the autocorrelation.
2. *Reflection.* The kernel is even and `A(−z) = conj (A z)`, so `A` may be replaced by
   `conj ∘ A`.
3. *Fourier inversion.* `conj ∘ A` is the forward Fourier transform of the momentum density
   `B(k) = 𝓕f(k) · conj (𝓕f(k))` (both `A` and `B` are integrable for Schwartz `f`).
4. *Multiplication formula.* `∫ C_S · 𝓕B = ∫ 𝓕C_S · B`, and `𝓕C_S = P`
   (`properTimeCovariance_fourier`), giving the momentum-space form.

## Contents

- proper-time kernel regularity: measurability, integrability of the `s`-slices, and
  continuity of `C_S` on `(0,∞)` — the analytic inputs for OS1 and OS4;
- the pairings `freeCovarianceℂ_bilinear` `= ∫∫ f(x) C(x,y) g(y)` and `freeCovarianceℂ`
  (sesquilinear), with product-space integrability (`freeCovarianceℂ_bilinear_integrable`);
- the Parseval bridge `parseval_covariance_schwartz` and positivity `freeCovarianceℂ_positive`;
- time-reflection and Euclidean invariance of the kernel and of the double integrals;
- bilinearity of the pairing (additivity/homogeneity in each slot, symmetry);
- the momentum weights `freePropagatorMom` and `freePropagatorMomSqrt = 1/√((2π)²‖k‖²+m²)`
  with the `L∞`-multiplier machinery used by the square-root propagator embedding;
- the centered kernel `freeCovarianceKernel d m z = C(0,z)` with continuity off the origin,
  integrability, and exponential/polynomial decay beyond unit radius — the OS4 inputs.
-/

open MeasureTheory Complex OSforGFF
open scoped RealInnerProductSpace

noncomputable section

namespace OSforGFF

/-- The proper-time covariance is a measurable function of the radius. -/
lemma properTimeCovariance_measurable (d : ℕ) (m : ℝ) :
    Measurable (properTimeCovariance d m) := by
  have h : StronglyMeasurable (Function.uncurry fun (r t : ℝ) =>
      Real.exp (-t * m ^ 2) * heatKernelProfile d t r) := by
    apply Measurable.stronglyMeasurable
    unfold Function.uncurry heatKernelProfile
    fun_prop
  exact (h.integral_prod_right' (ν := volume.restrict (Set.Ioi 0))).measurable

/-- `x ↦ C_S(‖x‖)` is measurable on `ℝ^d`. -/
lemma properTimeCovariance_norm_measurable (d : ℕ) (m : ℝ) :
    Measurable fun x : EuclideanSpace ℝ (Fin d) => properTimeCovariance d m ‖x‖ :=
  (properTimeCovariance_measurable d m).comp measurable_norm

/-- For `r > 0`, the proper-time integrand `t ↦ e^{-t m²} H_d(t, r)` is integrable on `(0, ∞)`:
    the heat-kernel singularity `t^{-d/2}` at `t = 0` is suppressed by `e^{-r²/(4t)}`. -/
lemma properTime_slice_integrableOn (d : ℕ) (m : ℝ) (hm : 0 < m) {r : ℝ} (hr : 0 < r) :
    MeasureTheory.IntegrableOn
      (fun t => Real.exp (-t * m ^ 2) * heatKernelProfile d t r) (Set.Ioi 0) := by
  have hgi : MeasureTheory.IntegrableOn
      (fun t => t ^ ((d : ℝ) / 2) * Real.exp (-m ^ 2 * t)) (Set.Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow (s := (d : ℝ) / 2) (p := 1) (b := m ^ 2)
      (by have h2 : (0 : ℝ) ≤ (d : ℝ) / 2 := (by positivity); linarith) (by norm_num) (by positivity)
    simpa [Real.rpow_one] using this
  refine (hgi.const_mul ((4 * Real.pi) ^ (-(d : ℝ) / 2)
    * ((d.factorial : ℝ) * (4 / r ^ 2) ^ d))).mono' ?_ ?_
  · unfold heatKernelProfile
    exact ((by fun_prop : Measurable fun t : ℝ =>
      Real.exp (-t * m ^ 2) * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2)
        * Real.exp (-r ^ 2 / (4 * t))))).aestronglyMeasurable
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) < t := ht
    unfold heatKernelProfile
    rw [Real.norm_of_nonneg (by positivity)]
    have hexp : Real.exp (-r ^ 2 / (4 * t)) ≤ (d.factorial : ℝ) * (4 / r ^ 2) ^ d * t ^ d := by
      have hx : (0 : ℝ) ≤ r ^ 2 / (4 * t) := by positivity
      have h := Real.pow_div_factorial_le_exp (r ^ 2 / (4 * t)) hx d
      have hlow : (0 : ℝ) < (r ^ 2 / (4 * t)) ^ d / d.factorial := by positivity
      rw [show -r ^ 2 / (4 * t) = -(r ^ 2 / (4 * t)) by ring, Real.exp_neg]
      calc (Real.exp (r ^ 2 / (4 * t)))⁻¹
          ≤ ((r ^ 2 / (4 * t)) ^ d / d.factorial)⁻¹ := inv_anti₀ hlow h
        _ = (d.factorial : ℝ) * (4 / r ^ 2) ^ d * t ^ d := by
            rw [inv_div, div_pow, div_div_eq_mul_div, div_pow]
            field_simp
            ring
    have htd : t ^ (-(d : ℝ) / 2) * (t : ℝ) ^ d = t ^ ((d : ℝ) / 2) := by
      rw [← Real.rpow_natCast t d, ← Real.rpow_add ht0]
      ring_nf
    calc Real.exp (-t * m ^ 2) * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2)
            * Real.exp (-r ^ 2 / (4 * t)))
        ≤ Real.exp (-t * m ^ 2) * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2)
            * ((d.factorial : ℝ) * (4 / r ^ 2) ^ d * t ^ d)) := by
          have h4 : (0 : ℝ) ≤ (4 * Real.pi * t) ^ (-(d : ℝ) / 2) :=
            Real.rpow_nonneg (by positivity) _
          have := mul_le_mul_of_nonneg_left hexp h4
          exact mul_le_mul_of_nonneg_left this (Real.exp_nonneg _)
      _ = (4 * Real.pi) ^ (-(d : ℝ) / 2) * ((d.factorial : ℝ) * (4 / r ^ 2) ^ d)
            * (t ^ ((d : ℝ) / 2) * Real.exp (-m ^ 2 * t)) := by
          rw [Real.mul_rpow (by positivity) ht0.le, ← htd]
          ring_nf

/-- The proper-time covariance is continuous on `(0, ∞)` (dominated convergence over the
    proper-time integral, with the dominator taken at radius `r₀/2`). -/
lemma properTimeCovariance_continuousOn (d : ℕ) (m : ℝ) (hm : 0 < m) :
    ContinuousOn (properTimeCovariance d m) (Set.Ioi 0) := by
  intro r₀ hr₀
  have hr₀' : (0 : ℝ) < r₀ := hr₀
  have hhalf : (0 : ℝ) < r₀ / 2 := by positivity
  have hCA : ContinuousAt (fun r => ∫ t in Set.Ioi (0 : ℝ),
      Real.exp (-t * m ^ 2) * heatKernelProfile d t r) r₀ := by
    refine MeasureTheory.continuousAt_of_dominated ?_ ?_
      (properTime_slice_integrableOn d m hm hhalf) ?_
    · filter_upwards with r
      unfold heatKernelProfile
      exact ((by fun_prop : Measurable fun t : ℝ =>
        Real.exp (-t * m ^ 2) * ((4 * Real.pi * t) ^ (-(d : ℝ) / 2)
          * Real.exp (-r ^ 2 / (4 * t))))).aestronglyMeasurable
    · filter_upwards [eventually_gt_nhds (by linarith : r₀ / 2 < r₀)] with r hr
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      unfold heatKernelProfile
      rw [Real.norm_of_nonneg (by positivity)]
      have hmono : Real.exp (-r ^ 2 / (4 * t)) ≤ Real.exp (-(r₀ / 2) ^ 2 / (4 * t)) := by
        apply Real.exp_le_exp.mpr
        have h2 : (0 : ℝ) < 4 * t := by linarith
        gcongr
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg (by positivity) _))
        (Real.exp_nonneg _)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : (0 : ℝ) < t := ht
      unfold heatKernelProfile
      fun_prop
  exact hCA.continuousWithinAt

end OSforGFF

/-- The complex covariance bilinear pairing of two complex test functions against the
    free-covariance kernel: `⟨f, C g⟩ = ∫∫ f(x) · C(x, y) · g(y) dx dy`. -/
def freeCovarianceℂ_bilinear {d : ℕ} (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)]
    [GFFPropagator d m] (f g : SchwartzTestFunctionℂ d) : ℂ :=
  ∫ x, ∫ y, f x * (freeCovariance d m x y : ℂ) * g y

/-- The complex covariance sesquilinear pairing:
    `⟨f, C ḡ⟩ = ∫∫ f(x) · C(x, y) · conj (g y) dx dy`. -/
def freeCovarianceℂ {d : ℕ} (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)]
    [GFFPropagator d m] (f g : SchwartzTestFunctionℂ d) : ℂ :=
  ∫ x, ∫ y, f x * (freeCovariance d m x y : ℂ) * (starRingEnd ℂ (g y))

section ProperTimeKernel

variable {d : ℕ} {m : ℝ} [Fact (0 < m)] [Fact (2 ≤ d)]

/-- The diagonal `{(x, y) | x = y}` is null for the product volume. -/
lemma diagonal_null_prod :
    ((volume : Measure (SpaceTime d)).prod volume)
      {p : SpaceTime d × SpaceTime d | p.1 - p.2 = 0} = 0 := by
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (SpaceTime d) := inferInstance
  have hmeas : MeasurableSet {p : SpaceTime d × SpaceTime d | p.1 - p.2 = 0} :=
    (measurable_fst.sub measurable_snd) (measurableSet_singleton 0)
  rw [Measure.prod_apply hmeas]
  have hslice : ∀ x : SpaceTime d,
      (Prod.mk x ⁻¹' {p : SpaceTime d × SpaceTime d | p.1 - p.2 = 0}) = {x} := by
    intro x
    ext y
    simp [sub_eq_zero, eq_comm]
  simp [hslice]

/-- Away from the (null) diagonal the covariance kernel agrees with the proper-time kernel:
    a.e.-equality on the product space. -/
lemma freeCovariance_ae_properTime [GFFPropagator d m] :
    (fun p : SpaceTime d × SpaceTime d => freeCovariance d m p.1 p.2)
      =ᵐ[(volume : Measure (SpaceTime d)).prod volume]
    fun p => properTimeCovariance d m ‖p.1 - p.2‖ := by
  filter_upwards [compl_mem_ae_iff.mpr (diagonal_null_prod (d := d))] with p hp
  have hne : p.1 - p.2 ≠ 0 := hp
  unfold freeCovariance
  exact GFFPropagator.schwinger_eq ‖p.1 - p.2‖ (norm_pos_iff.mpr hne)

omit [Fact (2 ≤ d)] in
/-- The Schwartz-pair integrand against the proper-time kernel is integrable on the product
    space: the bound `‖f‖_∞ · C_S(‖x − y‖) · ‖g(y)‖` is a shear transport of a product of
    integrable functions. -/
lemma properTime_bilinear_integrable (f g : SchwartzTestFunctionℂ d) :
    Integrable (fun p : SpaceTime d × SpaceTime d =>
      f p.1 * (properTimeCovariance d m ‖p.1 - p.2‖ : ℂ) * g p.2)
      ((volume : Measure (SpaceTime d)).prod volume) := by
  have hm : (0 : ℝ) < m := Fact.out
  obtain ⟨M, hM0, hMd⟩ := f.decay 0 0
  have hM : ∀ x, ‖f x‖ ≤ M := by
    intro x
    have := hMd x
    simpa [norm_iteratedFDeriv_zero] using this
  have hCS : Integrable (fun z : SpaceTime d => properTimeCovariance d m ‖z‖) :=
    properTimeCovariance_integrable d m hm
  have hgM : Integrable (fun y : SpaceTime d => M * ‖g y‖) := g.integrable.norm.const_mul M
  have hprod : Integrable (fun q : SpaceTime d × SpaceTime d =>
      properTimeCovariance d m ‖q.1‖ * (M * ‖g q.2‖))
      ((volume : Measure (SpaceTime d)).prod volume) := hCS.mul_prod hgM
  have hshear : Integrable (fun p : SpaceTime d × SpaceTime d =>
      properTimeCovariance d m ‖p.1 - p.2‖ * (M * ‖g p.2‖))
      ((volume : Measure (SpaceTime d)).prod volume) := by
    have h := (measurePreserving_sub_prod (volume : Measure (SpaceTime d))
      volume).integrable_comp_of_integrable hprod
    simpa [Function.comp_def] using h
  have hmeas : AEStronglyMeasurable (fun p : SpaceTime d × SpaceTime d =>
      f p.1 * (properTimeCovariance d m ‖p.1 - p.2‖ : ℂ) * g p.2)
      ((volume : Measure (SpaceTime d)).prod volume) := by
    refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ ?_) ?_
    · exact f.continuous.aestronglyMeasurable.comp_fst
    · exact (Complex.measurable_ofReal.comp ((properTimeCovariance_norm_measurable d m).comp
        (measurable_fst.sub measurable_snd))).aestronglyMeasurable
    · exact g.continuous.aestronglyMeasurable.comp_snd
  refine hshear.mono' hmeas ?_
  filter_upwards with p
  have h1 : 0 ≤ properTimeCovariance d m ‖p.1 - p.2‖ := properTimeCovariance_nonneg _ _ _
  calc ‖f p.1 * (properTimeCovariance d m ‖p.1 - p.2‖ : ℂ) * g p.2‖
      = ‖f p.1‖ * properTimeCovariance d m ‖p.1 - p.2‖ * ‖g p.2‖ := by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg h1]
    _ ≤ M * properTimeCovariance d m ‖p.1 - p.2‖ * ‖g p.2‖ := by
        gcongr
        exact hM p.1
    _ = properTimeCovariance d m ‖p.1 - p.2‖ * (M * ‖g p.2‖) := by ring

end ProperTimeKernel

/-- The bilinear-pairing integrand is integrable on the product space. -/
theorem freeCovarianceℂ_bilinear_integrable {d : ℕ} (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)]
    [GFFPropagator d m] (f g : SchwartzTestFunctionℂ d) :
    Integrable (fun p : SpaceTime d × SpaceTime d =>
      f p.1 * (freeCovariance d m p.1 p.2 : ℂ) * g p.2) volume := by
  rw [Measure.volume_eq_prod]
  refine (properTime_bilinear_integrable (m := m) f g).congr ?_
  filter_upwards [freeCovariance_ae_properTime (d := d) (m := m)] with p hp
  rw [hp]

/-! ### The autocorrelation and the momentum-space identity -/

/-- The autocorrelation of a Schwartz function: `A(z) = ∫ f(x) · conj (f (x − z))`. -/
def schwartzAutocorr {d : ℕ} (f : SchwartzTestFunctionℂ d) (z : SpaceTime d) : ℂ :=
  ∫ x : SpaceTime d, f x * starRingEnd ℂ (f (x - z))

section Autocorr

variable {d : ℕ} {m : ℝ} [Fact (0 < m)] [Fact (2 ≤ d)]

omit [Fact (0 < m)] [Fact (2 ≤ d)] in
/-- Conjugated autocorrelation as an integral: `conj (A z) = ∫ conj (f x) · f (x − z)`. -/
lemma schwartzAutocorr_conj (f : SchwartzTestFunctionℂ d) (z : SpaceTime d) :
    starRingEnd ℂ (schwartzAutocorr f z)
      = ∫ x : SpaceTime d, starRingEnd ℂ (f x) * f (x - z) := by
  unfold schwartzAutocorr
  refine Eq.trans
    (integral_conj (f := fun x : SpaceTime d => f x * starRingEnd ℂ (f (x - z)))).symm ?_
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp only [map_mul, Complex.conj_conj])

omit [Fact (0 < m)] [Fact (2 ≤ d)] in
/-- Reflecting the autocorrelation argument conjugates its value: `A(−z) = conj (A z)`. -/
lemma schwartzAutocorr_neg (f : SchwartzTestFunctionℂ d) (z : SpaceTime d) :
    schwartzAutocorr f (-z) = starRingEnd ℂ (schwartzAutocorr f z) := by
  rw [schwartzAutocorr_conj]
  unfold schwartzAutocorr
  rw [← integral_add_right_eq_self (fun x => starRingEnd ℂ (f x) * f (x - z)) z]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    simp only [sub_neg_eq_add, add_sub_cancel_right]
    ring)

omit [Fact (0 < m)] [Fact (2 ≤ d)] in
/-- The complex coercion of `𝐞` is multiplicative. -/
private lemma fourierChar_coe_mul (a b : ℝ) :
    (Real.fourierChar a : ℂ) * (Real.fourierChar b : ℂ) = (Real.fourierChar (a + b) : ℂ) := by
  rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul]

omit [Fact (0 < m)] [Fact (2 ≤ d)] in
/-- Complex conjugation reflects the character: `conj (𝐞 r) = 𝐞 (−r)`. -/
private lemma fourierChar_coe_conj (r : ℝ) :
    starRingEnd ℂ (Real.fourierChar r : ℂ) = (Real.fourierChar (-r) : ℂ) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

omit [Fact (0 < m)] [Fact (2 ≤ d)] in
/-- The squared-modulus function `k ↦ 𝓕f(k) · conj (𝓕f(k))` of the Fourier transform of a
    Schwartz function is integrable. -/
lemma fourier_normSq_integrable (f : SchwartzTestFunctionℂ d) :
    Integrable (fun k : SpaceTime d =>
      (SchwartzMap.fourierTransformCLM ℂ f) k
        * starRingEnd ℂ ((SchwartzMap.fourierTransformCLM ℂ f) k)) := by
  set F := SchwartzMap.fourierTransformCLM ℂ f with hF
  obtain ⟨M, hM0, hMd⟩ := F.decay 0 0
  refine F.integrable.mul_bdd (c := M)
    (Complex.continuous_conj.comp F.continuous).aestronglyMeasurable ?_
  filter_upwards with k
  have := hMd k
  simpa [norm_iteratedFDeriv_zero, RCLike.norm_conj] using this

omit [Fact (0 < m)] [Fact (2 ≤ d)] in
/-- The Fourier transform of `k ↦ 𝓕f(k) · conj (𝓕f(k))` is the conjugated autocorrelation:
    `𝓕[𝓕f · conj (𝓕f)](z) = conj (A(z))` (Fubini against the character, then Fourier
    inversion of the Schwartz function). -/
lemma fourier_normSq_eq_conj_autocorr (f : SchwartzTestFunctionℂ d) (z : SpaceTime d) :
    FourierTransform.fourier (fun k : SpaceTime d =>
        (SchwartzMap.fourierTransformCLM ℂ f) k
          * starRingEnd ℂ ((SchwartzMap.fourierTransformCLM ℂ f) k)) z
      = starRingEnd ℂ (schwartzAutocorr f z) := by
  set F := SchwartzMap.fourierTransformCLM ℂ f with hFdef
  have hFapp : ∀ w : SpaceTime d,
      F w = ∫ y : SpaceTime d, (Real.fourierChar (-⟪y, w⟫) : ℂ) * f y := by
    intro w
    have h0 : F w = FourierTransform.fourier (⇑f) w := rfl
    rw [h0, Real.fourier_eq]
    simp_rw [Circle.smul_def, smul_eq_mul]
  have hconjF : ∀ k : SpaceTime d, starRingEnd ℂ (F k)
      = ∫ y : SpaceTime d, (Real.fourierChar ⟪y, k⟫ : ℂ) * starRingEnd ℂ (f y) := by
    intro k
    rw [hFapp k]
    refine Eq.trans (integral_conj (f := fun y : SpaceTime d =>
      (Real.fourierChar (-⟪y, k⟫) : ℂ) * f y)).symm ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
      simp only [map_mul, fourierChar_coe_conj, neg_neg])
  have hdouble : ∀ w : SpaceTime d,
      FourierTransform.fourier (F : SpaceTime d → ℂ) w = f (-w) := by
    intro w
    have h1 : FourierTransform.fourier (F : SpaceTime d → ℂ) w
        = FourierTransform.fourierInv (FourierTransform.fourier (⇑f)) (-w) := by
      rw [Real.fourierInv_eq_fourier_neg, neg_neg]
      rfl
    rw [h1]
    exact f.integrable.fourierInv_fourier_eq F.integrable f.continuous.continuousAt
  have hGint : Integrable (Function.uncurry fun (k y : SpaceTime d) =>
      starRingEnd ℂ (f y) * ((Real.fourierChar (-⟪k, z - y⟫) : ℂ) * F k))
      ((volume : Measure (SpaceTime d)).prod volume) := by
    have hdom : Integrable (fun q : SpaceTime d × SpaceTime d => ‖F q.1‖ * ‖f q.2‖)
        ((volume : Measure (SpaceTime d)).prod volume) :=
      F.integrable.norm.mul_prod f.integrable.norm
    have hcont : Continuous (Function.uncurry fun (k y : SpaceTime d) =>
        starRingEnd ℂ (f y) * ((Real.fourierChar (-⟪k, z - y⟫) : ℂ) * F k)) := by
      apply Continuous.mul
      · exact Complex.continuous_conj.comp (f.continuous.comp continuous_snd)
      · apply Continuous.mul
        · exact continuous_subtype_val.comp (Real.continuous_fourierChar.comp
            (continuous_fst.inner (continuous_const.sub continuous_snd)).neg)
        · exact F.continuous.comp continuous_fst
    refine hdom.mono' hcont.aestronglyMeasurable ?_
    filter_upwards with q
    obtain ⟨k, y⟩ := q
    simp only [Function.uncurry_apply_pair, norm_mul, RCLike.norm_conj, Circle.norm_coe, one_mul]
    exact le_of_eq (mul_comm _ _)
  have hexp : FourierTransform.fourier
      (fun k : SpaceTime d => F k * starRingEnd ℂ (F k)) z
      = ∫ k : SpaceTime d, ∫ y : SpaceTime d,
          starRingEnd ℂ (f y) * ((Real.fourierChar (-⟪k, z - y⟫) : ℂ) * F k) := by
    rw [Real.fourier_eq]
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [Circle.smul_def, smul_eq_mul]
    calc (Real.fourierChar (-⟪k, z⟫) : ℂ) * (F k * starRingEnd ℂ (F k))
        = ((Real.fourierChar (-⟪k, z⟫) : ℂ) * F k) * starRingEnd ℂ (F k) := by ring
      _ = ((Real.fourierChar (-⟪k, z⟫) : ℂ) * F k)
            * ∫ y : SpaceTime d, (Real.fourierChar ⟪y, k⟫ : ℂ) * starRingEnd ℂ (f y) := by
          rw [hconjF k]
      _ = ∫ y : SpaceTime d, ((Real.fourierChar (-⟪k, z⟫) : ℂ) * F k)
            * ((Real.fourierChar ⟪y, k⟫ : ℂ) * starRingEnd ℂ (f y)) :=
          (MeasureTheory.integral_const_mul _ _).symm
      _ = ∫ y : SpaceTime d,
            starRingEnd ℂ (f y) * ((Real.fourierChar (-⟪k, z - y⟫) : ℂ) * F k) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          have hchar : (Real.fourierChar (-⟪k, z⟫) : ℂ) * (Real.fourierChar ⟪y, k⟫ : ℂ)
              = (Real.fourierChar (-⟪k, z - y⟫) : ℂ) := by
            rw [fourierChar_coe_mul]
            congr 2
            rw [inner_sub_right, real_inner_comm y k]
            ring
          calc ((Real.fourierChar (-⟪k, z⟫) : ℂ) * F k)
                * ((Real.fourierChar ⟪y, k⟫ : ℂ) * starRingEnd ℂ (f y))
              = starRingEnd ℂ (f y) * (((Real.fourierChar (-⟪k, z⟫) : ℂ)
                  * (Real.fourierChar ⟪y, k⟫ : ℂ)) * F k) := by ring
            _ = starRingEnd ℂ (f y) * ((Real.fourierChar (-⟪k, z - y⟫) : ℂ) * F k) := by
                rw [hchar]
  rw [hexp, MeasureTheory.integral_integral_swap hGint]
  have hinner : ∀ y : SpaceTime d,
      (∫ k : SpaceTime d, starRingEnd ℂ (f y)
          * ((Real.fourierChar (-⟪k, z - y⟫) : ℂ) * F k))
        = starRingEnd ℂ (f y) * f (y - z) := by
    intro y
    calc (∫ k : SpaceTime d, starRingEnd ℂ (f y)
            * ((Real.fourierChar (-⟪k, z - y⟫) : ℂ) * F k))
        = starRingEnd ℂ (f y)
            * ∫ k : SpaceTime d, (Real.fourierChar (-⟪k, z - y⟫) : ℂ) * F k :=
          MeasureTheory.integral_const_mul _ _
      _ = starRingEnd ℂ (f y) * f (y - z) := by
          have h2 : (∫ k : SpaceTime d, (Real.fourierChar (-⟪k, z - y⟫) : ℂ) * F k)
              = FourierTransform.fourier (F : SpaceTime d → ℂ) (z - y) := by
            rw [Real.fourier_eq]
            simp_rw [Circle.smul_def, smul_eq_mul]
          rw [h2, hdouble (z - y), neg_sub]
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner), schwartzAutocorr_conj]

omit [Fact (2 ≤ d)] in
/-- Fubini/shear form of the proper-time sesquilinear pairing: the pairing collapses against
    the autocorrelation, `∫∫ f(x) C_S(‖x−y‖) conj (f y) = ∫ C_S(‖z‖) · A(z)`. -/
lemma properTime_pairing_eq_autocorr (f : SchwartzTestFunctionℂ d) :
    (∫ x, ∫ y, f x * (properTimeCovariance d m ‖x - y‖ : ℂ) * starRingEnd ℂ (f y))
      = ∫ z, (properTimeCovariance d m ‖z‖ : ℂ) * schwartzAutocorr f z := by
  have hm : (0 : ℝ) < m := Fact.out
  obtain ⟨M, hM0, hMd⟩ := f.decay 0 0
  have hM : ∀ x, ‖f x‖ ≤ M := by
    intro x
    have := hMd x
    simpa [norm_iteratedFDeriv_zero] using this
  have hCS : Integrable (fun z : SpaceTime d => properTimeCovariance d m ‖z‖) :=
    properTimeCovariance_integrable d m hm
  -- joint integrability of `(x, z) ↦ f(x) · C_S(‖z‖) · conj (f (x − z))`
  have hJ : Integrable (fun p : SpaceTime d × SpaceTime d =>
      f p.1 * (properTimeCovariance d m ‖p.2‖ : ℂ) * starRingEnd ℂ (f (p.1 - p.2)))
      ((volume : Measure (SpaceTime d)).prod volume) := by
    have hdom : Integrable (fun p : SpaceTime d × SpaceTime d =>
        ‖f p.1‖ * (M * properTimeCovariance d m ‖p.2‖))
        ((volume : Measure (SpaceTime d)).prod volume) :=
      f.integrable.norm.mul_prod (hCS.const_mul M)
    have hmeas : AEStronglyMeasurable (fun p : SpaceTime d × SpaceTime d =>
        f p.1 * (properTimeCovariance d m ‖p.2‖ : ℂ) * starRingEnd ℂ (f (p.1 - p.2)))
        ((volume : Measure (SpaceTime d)).prod volume) := by
      refine AEStronglyMeasurable.mul (AEStronglyMeasurable.mul ?_ ?_) ?_
      · exact f.continuous.aestronglyMeasurable.comp_fst
      · exact (Complex.measurable_ofReal.comp ((properTimeCovariance_norm_measurable d m).comp
          measurable_snd)).aestronglyMeasurable
      · exact (Complex.continuous_conj.comp
          (f.continuous.comp (continuous_fst.sub continuous_snd))).aestronglyMeasurable
    refine hdom.mono' hmeas ?_
    filter_upwards with p
    have h1 : 0 ≤ properTimeCovariance d m ‖p.2‖ := properTimeCovariance_nonneg _ _ _
    calc ‖f p.1 * (properTimeCovariance d m ‖p.2‖ : ℂ) * starRingEnd ℂ (f (p.1 - p.2))‖
        = ‖f p.1‖ * properTimeCovariance d m ‖p.2‖ * ‖f (p.1 - p.2)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg h1, RCLike.norm_conj]
      _ ≤ ‖f p.1‖ * properTimeCovariance d m ‖p.2‖ * M := by
          gcongr
          exact hM _
      _ = ‖f p.1‖ * (M * properTimeCovariance d m ‖p.2‖) := by ring
  -- inner change of variables `y := x − z` at each fixed `x`
  have hinner : ∀ x : SpaceTime d,
      (∫ y, f x * (properTimeCovariance d m ‖x - y‖ : ℂ) * starRingEnd ℂ (f y))
        = ∫ z, f x * (properTimeCovariance d m ‖z‖ : ℂ) * starRingEnd ℂ (f (x - z)) := by
    intro x
    rw [← integral_sub_left_eq_self
      (fun z => f x * (properTimeCovariance d m ‖z‖ : ℂ) * starRingEnd ℂ (f (x - z)))
      (volume : Measure (SpaceTime d)) x]
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => by
      simp only [sub_sub_cancel])
  rw [integral_congr_ae (Filter.Eventually.of_forall hinner)]
  -- swap the two integrals and collapse the inner one to the autocorrelation
  rw [MeasureTheory.integral_integral_swap hJ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  unfold schwartzAutocorr
  calc (∫ x, f x * (properTimeCovariance d m ‖z‖ : ℂ) * starRingEnd ℂ (f (x - z)))
      = ∫ x, (properTimeCovariance d m ‖z‖ : ℂ) * (f x * starRingEnd ℂ (f (x - z))) :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
    _ = (properTimeCovariance d m ‖z‖ : ℂ) * ∫ x, f x * starRingEnd ℂ (f (x - z)) :=
        MeasureTheory.integral_const_mul _ _

end Autocorr

section Parseval

variable {d : ℕ} {m : ℝ} [Fact (0 < m)] [Fact (2 ≤ d)] [GFFPropagator d m]

/-- The sesquilinear pairing with the `freeCovariance` kernel agrees with the proper-time
    kernel pairing (the kernels agree away from the null diagonal). -/
lemma freeCovarianceℂ_self_eq_properTime (f : SchwartzTestFunctionℂ d) :
    freeCovarianceℂ m f f
      = ∫ x, ∫ y, f x * (properTimeCovariance d m ‖x - y‖ : ℂ) * starRingEnd ℂ (f y) := by
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  have : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have : Nontrivial (SpaceTime d) := inferInstance
  unfold freeCovarianceℂ
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  refine integral_congr_ae ?_
  filter_upwards [compl_mem_ae_iff.mpr (measure_singleton x)] with y hy
  have hxy : x - y ≠ 0 := sub_ne_zero.mpr fun h => hy (h ▸ rfl)
  unfold freeCovariance
  rw [GFFPropagator.schwinger_eq ‖x - y‖ (norm_pos_iff.mpr hxy)]

/-- **The complex Parseval identity for the covariance pairing**: the quadratic pairing
    equals the (real, nonnegative) momentum-space integral of `‖𝓕f‖²` against the propagator,
    `⟨f, C f̄⟩ = ∫ ‖𝓕f(k)‖² · P(k) dk`. -/
theorem freeCovarianceℂ_self_eq_momentum (f : SchwartzTestFunctionℂ d) :
    freeCovarianceℂ m f f
      = ((∫ k : SpaceTime d, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖ ^ 2
          * freePropagatorMom d m k : ℝ) : ℂ) := by
  have hm : (0 : ℝ) < m := Fact.out
  have hCSint : Integrable (fun x : SpaceTime d => (properTimeCovariance d m ‖x‖ : ℂ)) :=
    (properTimeCovariance_integrable d m hm).ofReal
  have hBint : Integrable (fun k : SpaceTime d =>
      (SchwartzMap.fourierTransformCLM ℂ f) k
        * starRingEnd ℂ ((SchwartzMap.fourierTransformCLM ℂ f) k)) :=
    fourier_normSq_integrable f
  -- reflect `z ↦ −z`: the kernel is even and the autocorrelation reflects to its conjugate
  have h2 : (∫ z : SpaceTime d, (properTimeCovariance d m ‖z‖ : ℂ) * schwartzAutocorr f z)
      = ∫ z : SpaceTime d,
          (properTimeCovariance d m ‖z‖ : ℂ) * starRingEnd ℂ (schwartzAutocorr f z) := by
    refine Eq.trans (integral_neg_eq_self
      (fun z : SpaceTime d => (properTimeCovariance d m ‖z‖ : ℂ) * schwartzAutocorr f z)
      (volume : Measure (SpaceTime d))).symm ?_
    exact integral_congr_ae (Filter.Eventually.of_forall fun z => by
      simp only [norm_neg, schwartzAutocorr_neg])
  -- replace the conjugated autocorrelation by the Fourier transform of `‖𝓕f‖²`
  have h3 : (∫ z : SpaceTime d,
        (properTimeCovariance d m ‖z‖ : ℂ) * starRingEnd ℂ (schwartzAutocorr f z))
      = ∫ z : SpaceTime d, (properTimeCovariance d m ‖z‖ : ℂ)
          * FourierTransform.fourier (fun k : SpaceTime d =>
              (SchwartzMap.fourierTransformCLM ℂ f) k
                * starRingEnd ℂ ((SchwartzMap.fourierTransformCLM ℂ f) k)) z :=
    integral_congr_ae (Filter.Eventually.of_forall fun z =>
      congrArg ((properTimeCovariance d m ‖z‖ : ℂ) * ·)
        (fourier_normSq_eq_conj_autocorr f z).symm)
  -- the multiplication formula `∫ 𝓕C · B = ∫ C · 𝓕B`
  have h4 : (∫ k : SpaceTime d,
        FourierTransform.fourier
            (fun x : SpaceTime d => (properTimeCovariance d m ‖x‖ : ℂ)) k
          * ((SchwartzMap.fourierTransformCLM ℂ f) k
              * starRingEnd ℂ ((SchwartzMap.fourierTransformCLM ℂ f) k)))
      = ∫ z : SpaceTime d, (properTimeCovariance d m ‖z‖ : ℂ)
          * FourierTransform.fourier (fun k : SpaceTime d =>
              (SchwartzMap.fourierTransformCLM ℂ f) k
                * starRingEnd ℂ ((SchwartzMap.fourierTransformCLM ℂ f) k)) z := by
    have hL : Continuous fun p : SpaceTime d × SpaceTime d => (innerₗ (SpaceTime d)) p.1 p.2 :=
      continuous_inner
    have h := VectorFourier.integral_bilin_fourierIntegral_eq_flip
      (M := ContinuousLinearMap.mul ℂ ℂ) (e := Real.fourierChar)
      (L := innerₗ (SpaceTime d)) (μ := (volume : Measure (SpaceTime d)))
      (ν := (volume : Measure (SpaceTime d)))
      Real.continuous_fourierChar hL hCSint hBint
    rw [flip_innerₗ] at h
    exact h
  -- evaluate `𝓕C = P` and `B = ‖𝓕f‖²` pointwise
  have h5 : (∫ k : SpaceTime d,
        FourierTransform.fourier
            (fun x : SpaceTime d => (properTimeCovariance d m ‖x‖ : ℂ)) k
          * ((SchwartzMap.fourierTransformCLM ℂ f) k
              * starRingEnd ℂ ((SchwartzMap.fourierTransformCLM ℂ f) k)))
      = ((∫ k : SpaceTime d, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖ ^ 2
          * freePropagatorMom d m k : ℝ) : ℂ) := by
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall fun k => ?_))
      integral_complex_ofReal
    simp only [properTimeCovariance_fourier d m hm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring
  exact ((freeCovarianceℂ_self_eq_properTime f).trans
    (properTime_pairing_eq_autocorr f)).trans (h2.trans (h3.trans (h4.symm.trans h5)))

/-- **Parseval identity** for the covariance pairing, real form: the real part of the
    quadratic pairing is the momentum-space integral `∫ ‖𝓕f(k)‖² · P(k) dk`. -/
theorem parseval_covariance_schwartz (f : SchwartzTestFunctionℂ d) :
    (freeCovarianceℂ m f f).re
      = ∫ k : SpaceTime d, ‖(SchwartzMap.fourierTransformCLM ℂ f) k‖ ^ 2
          * freePropagatorMom d m k := by
  rw [freeCovarianceℂ_self_eq_momentum f]
  exact Complex.ofReal_re _

/-- Positivity of the covariance pairing: `0 ≤ Re ⟨f, C f̄⟩`. -/
theorem freeCovarianceℂ_positive (f : SchwartzTestFunctionℂ d) :
    0 ≤ (freeCovarianceℂ m f f).re := by
  rw [parseval_covariance_schwartz f]
  refine integral_nonneg fun k => mul_nonneg (sq_nonneg _) ?_
  unfold OSforGFF.freePropagatorMom
  positivity

end Parseval

/-! ### Real-valued test functions and time reflection -/

section ReflectionBasics

variable {d : ℕ}

/-- The complexification of a real test function is fixed by complex conjugation. -/
lemma toComplex_star_eq (f : SchwartzTestFunction d) (x : SpaceTime d) :
    starRingEnd ℂ ((toComplex f) x) = (toComplex f) x := by
  simp only [toComplex_apply]
  exact Complex.conj_ofReal (f x)

/-- The real part of a complex integral of (the coercion of) a real-valued function is the
    real integral. -/
lemma re_integral_ofReal {α : Type*} [MeasurableSpace α] (μ : Measure α) (h : α → ℝ)
    (_hf : Integrable h μ) :
    (∫ x, (h x : ℂ) ∂μ).re = ∫ x, h x ∂μ := by
  have h1 : (∫ x, (h x : ℂ) ∂μ) = ((∫ x, h x ∂μ : ℝ) : ℂ) := integral_ofReal
  rw [h1]
  exact Complex.ofReal_re _

variable [Fact (2 ≤ d)]

/-- Complexification commutes with composition by time reflection. -/
lemma compTimeReflection_toComplex_eq_ofReal (f : SchwartzTestFunction d) (x : SpaceTime d) :
    (QFT.compTimeReflection (toComplex f)) x = ((QFT.compTimeReflectionReal f) x : ℂ) := by
  simp only [QFT.compTimeReflection, QFT.compTimeReflectionReal,
    SchwartzMap.compCLM_apply, Function.comp_apply, toComplex_apply]

/-- The time-reflected complexification of a real test function remains real-valued. -/
lemma compTimeReflection_toComplex_star_eq (f : SchwartzTestFunction d) (x : SpaceTime d) :
    starRingEnd ℂ ((QFT.compTimeReflection (toComplex f)) x)
      = (QFT.compTimeReflection (toComplex f)) x := by
  simp only [QFT.compTimeReflection, SchwartzMap.compCLM_apply, Function.comp_apply]
  exact toComplex_star_eq f (QFT.timeReflectionCLM x)

/-- Integrating over spacetime is unchanged when both variables are composed with geometric
    time reflection (measure preservation plus Fubini). -/
lemma double_integral_timeReflection
    (G : SpaceTime d → SpaceTime d → ℂ)
    (_hG : Integrable (fun p : SpaceTime d × SpaceTime d => G p.1 p.2) (volume.prod volume)) :
    ∫ x, ∫ y, G (QFT.timeReflection x) (QFT.timeReflection y) ∂volume ∂volume
      = ∫ x, ∫ y, G x y ∂volume ∂volume := by
  have hmp := QFT.timeReflection_measurePreserving (d := d)
  have hmeas := (QFT.timeReflectionLE (d := d)).toMeasurableEquiv.measurableEmbedding
  have h_inner : ∀ x, ∫ y, G x (QFT.timeReflection y) = ∫ y, G x y :=
    fun x => hmp.integral_comp hmeas (fun y => G x y)
  simp_rw [h_inner]
  exact hmp.integral_comp hmeas (fun x => ∫ y, G x y)

end ReflectionBasics

/-! ### Invariance of the covariance kernel and the kernel pairings -/

section KernelInvariance

variable {d : ℕ} {m : ℝ} [Fact (0 < m)] [Fact (2 ≤ d)] [GFFPropagator d m]

/-- Euclidean invariance of the free covariance: the kernel is radial and Euclidean motions
    preserve distances. -/
theorem freeCovariance_euclidean_invariant (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (g : QFT.E d) (x y : SpaceTime d) :
    freeCovariance d m (QFT.act g x) (QFT.act g y) = freeCovariance d m x y := by
  unfold freeCovariance
  have h_diff : QFT.act g x - QFT.act g y = g.R (x - y) := by simp [QFT.act]
  simp only [h_diff, g.R.norm_map]

/-- Time reflection as an element of the Euclidean group (rotation with no translation). -/
def timeReflectionE : QFT.E d := ⟨QFT.timeReflectionLE.toLinearIsometry, 0⟩

omit [Fact (0 < m)] [GFFPropagator d m] in
/-- The Euclidean action of `timeReflectionE` is geometric time reflection. -/
lemma act_timeReflectionE (x : SpaceTime d) :
    QFT.act (timeReflectionE (d := d)) x = QFT.timeReflection x := by
  simp only [timeReflectionE, QFT.act, add_zero, LinearIsometryEquiv.coe_toLinearIsometry]
  rfl

/-- Time-reflection invariance of the position-space covariance kernel. -/
lemma covariance_timeReflection_invariant (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    ∀ x y, freeCovariance d m (QFT.timeReflection x) (QFT.timeReflection y)
      = freeCovariance d m x y := by
  intro x y
  rw [← act_timeReflectionE x, ← act_timeReflectionE y]
  exact freeCovariance_euclidean_invariant m timeReflectionE x y

/-- Time-reflection change of variables for the covariance pairing: moving the reflection from
    the first test function to the kernel and the second test function. -/
lemma double_integral_timeReflection_covariance
    (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f g : SchwartzTestFunctionℂ d)
    (hf : Integrable (fun p : SpaceTime d × SpaceTime d =>
        (QFT.compTimeReflection f) p.1 * (freeCovariance d m p.1 p.2 : ℂ) * g p.2)
        (volume.prod volume)) :
    ∫ x, ∫ y,
        (QFT.compTimeReflection f) x * (freeCovariance d m x y : ℂ) * g y ∂volume ∂volume
      = ∫ x, ∫ y,
          f x * (freeCovariance d m (QFT.timeReflection x) (QFT.timeReflection y) : ℂ)
            * (QFT.compTimeReflection g) y ∂volume ∂volume := by
  have h_comp : ∀ h : SchwartzTestFunctionℂ d, ∀ x,
      (QFT.compTimeReflection h) x = h (QFT.timeReflection x) := by
    intro h x
    simp only [QFT.compTimeReflection, SchwartzMap.compCLM_apply, Function.comp_apply]
    rfl
  simp_rw [h_comp]
  have hinv : ∀ z : SpaceTime d, QFT.timeReflection (QFT.timeReflection z) = z := by
    intro z
    exact QFT.timeReflectionLE.left_inv z
  rw [← double_integral_timeReflection
    (fun x y => f (QFT.timeReflection x) * (freeCovariance d m x y : ℂ) * g y) hf]
  simp only [hinv]

/-- Integrability of the covariance pairing integrand with a time-reflected first argument. -/
lemma integrable_compTimeReflection_covariance
    (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : SchwartzTestFunctionℂ d) :
    Integrable (fun p : SpaceTime d × SpaceTime d =>
        (QFT.compTimeReflection f) p.1 * (freeCovariance d m p.1 p.2 : ℂ) * f p.2)
      (volume.prod volume) := by
  rw [← Measure.volume_eq_prod]
  exact freeCovarianceℂ_bilinear_integrable m (QFT.compTimeReflection f) f

/-- Integrability of the real covariance kernel pairing of a real test function. -/
lemma integrable_real_covariance_kernel
    (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : SchwartzTestFunction d) :
    Integrable (fun p : SpaceTime d × SpaceTime d =>
        (QFT.compTimeReflectionReal f) p.1 * freeCovariance d m p.1 p.2 * f p.2)
      (volume.prod volume) := by
  have h_complex := integrable_compTimeReflection_covariance m (toComplex f)
  have h_eq : (fun p : SpaceTime d × SpaceTime d =>
      (QFT.compTimeReflection (toComplex f)) p.1 * (freeCovariance d m p.1 p.2 : ℂ)
          * (toComplex f) p.2)
      = (fun p => (((QFT.compTimeReflectionReal f) p.1 : ℂ)
          * ((freeCovariance d m p.1 p.2 : ℝ) : ℂ) * ((f p.2 : ℝ) : ℂ))) := by
    ext p
    simp only [compTimeReflection_toComplex_eq_ofReal, toComplex_apply]
  rw [h_eq] at h_complex
  have h_re_eq : ∀ p : SpaceTime d × SpaceTime d,
      (((QFT.compTimeReflectionReal f) p.1 : ℂ) * ((freeCovariance d m p.1 p.2 : ℝ) : ℂ)
          * ((f p.2 : ℝ) : ℂ)).re
      = (QFT.compTimeReflectionReal f) p.1 * freeCovariance d m p.1 p.2 * f p.2 := by
    intro p
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  apply Integrable.mono' h_complex.norm
  · convert h_complex.aestronglyMeasurable.re using 2 with p
    exact (h_re_eq p).symm
  · filter_upwards with p
    have h_norm_eq : ‖((QFT.compTimeReflectionReal f) p.1 : ℂ)
          * ((freeCovariance d m p.1 p.2 : ℝ) : ℂ) * ((f p.2 : ℝ) : ℂ)‖
        = ‖(QFT.compTimeReflectionReal f) p.1 * freeCovariance d m p.1 p.2 * f p.2‖ := by
      simp only [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul]
    rw [← h_norm_eq]

/-- Fubini form of the real covariance kernel pairing over the product measure. -/
lemma integral_prod_real_covariance_kernel
    (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : SchwartzTestFunction d) :
    ∫ p : SpaceTime d × SpaceTime d,
        (QFT.compTimeReflectionReal f) p.1 * freeCovariance d m p.1 p.2 * f p.2
        ∂(volume.prod volume)
      = ∫ x, ∫ y,
          (QFT.compTimeReflectionReal f) x * freeCovariance d m x y * f y ∂volume ∂volume := by
  rw [MeasureTheory.integral_prod]
  exact integrable_real_covariance_kernel m f

/-- Fubini form of the complex covariance kernel pairing over the product measure. -/
lemma integral_prod_complex_covariance_kernel
    (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : SchwartzTestFunction d) :
    ∫ p : SpaceTime d × SpaceTime d,
        (QFT.compTimeReflection (toComplex f)) p.1 * (freeCovariance d m p.1 p.2 : ℂ)
          * (toComplex f) p.2 ∂(volume.prod volume)
      = ∫ x, ∫ y,
          (QFT.compTimeReflection (toComplex f)) x * (freeCovariance d m x y : ℂ)
            * (toComplex f) y ∂volume ∂volume := by
  rw [MeasureTheory.integral_prod]
  exact integrable_compTimeReflection_covariance m (toComplex f)

/-- The real reflected pairing is the real part of the complexified reflected pairing. -/
lemma real_integral_eq_complex_re
    (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : SchwartzTestFunction d) :
    ∫ x, ∫ y,
        (QFT.compTimeReflectionReal f) x * freeCovariance d m x y * f y ∂volume ∂volume
      = (∫ x, ∫ y, (QFT.compTimeReflection (toComplex f)) x * (freeCovariance d m x y : ℂ)
          * (toComplex f) y ∂volume ∂volume).re := by
  rw [← integral_prod_complex_covariance_kernel m f]
  have h_eq_prod : ∀ p : SpaceTime d × SpaceTime d,
      (QFT.compTimeReflection (toComplex f)) p.1 * (freeCovariance d m p.1 p.2 : ℂ)
          * (toComplex f) p.2
      = ((QFT.compTimeReflectionReal f) p.1 * freeCovariance d m p.1 p.2 * f p.2 : ℂ) := by
    intro p
    simp only [compTimeReflection_toComplex_eq_ofReal, toComplex_apply]
  simp_rw [h_eq_prod]
  simp only [← Complex.ofReal_mul]
  rw [← integral_prod_real_covariance_kernel m f]
  symm
  exact re_integral_ofReal (volume.prod volume)
    (fun p => (QFT.compTimeReflectionReal f) p.1 * freeCovariance d m p.1 p.2 * f p.2)
    (integrable_real_covariance_kernel m f)

end KernelInvariance

/-! ### Bilinearity of the covariance pairing -/

section BilinearAlgebra

variable {d : ℕ} {m : ℝ} [Fact (0 < m)] [Fact (2 ≤ d)] [GFFPropagator d m]

/-- For each fixed `x`, the outer integrand of the bilinear pairing is integrable. -/
lemma freeCovarianceℂ_bilinear_inner_integrable (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (f g : SchwartzTestFunctionℂ d) :
    Integrable (fun x => ∫ y, f x * (freeCovariance d m x y : ℂ) * g y ∂volume) volume := by
  have h := freeCovarianceℂ_bilinear_integrable m f g
  rw [Measure.volume_eq_prod] at h
  exact h.integral_prod_left

/-- For almost every `x`, the inner integrand of the bilinear pairing is integrable in `y`. -/
lemma freeCovarianceℂ_bilinear_slice_integrable (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (f g : SchwartzTestFunctionℂ d) :
    ∀ᵐ x ∂(volume : Measure (SpaceTime d)),
      Integrable (fun y => f x * (freeCovariance d m x y : ℂ) * g y) volume := by
  have h := freeCovarianceℂ_bilinear_integrable m f g
  rw [Measure.volume_eq_prod] at h
  exact h.prod_right_ae

/-- Bilinearity in the first argument: scalar multiplication and addition combined. -/
theorem freeCovarianceℂ_bilinear_add_smul_left (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (c : ℂ) (f₁ f₂ g : SchwartzTestFunctionℂ d) :
    freeCovarianceℂ_bilinear m (c • f₁ + f₂) g
      = c * freeCovarianceℂ_bilinear m f₁ g + freeCovarianceℂ_bilinear m f₂ g := by
  classical
  simp only [freeCovarianceℂ_bilinear]
  set F := fun x : SpaceTime d =>
    ∫ y, ((c • f₁ + f₂) x) * (freeCovariance d m x y : ℂ) * (g y) ∂volume
  set F₁ := fun x : SpaceTime d =>
    ∫ y, f₁ x * (freeCovariance d m x y : ℂ) * (g y) ∂volume
  set F₂ := fun x : SpaceTime d =>
    ∫ y, f₂ x * (freeCovariance d m x y : ℂ) * (g y) ∂volume
  have hF₁ : Integrable F₁ volume :=
    freeCovarianceℂ_bilinear_inner_integrable m f₁ g
  have hF₂ : Integrable F₂ volume :=
    freeCovarianceℂ_bilinear_inner_integrable m f₂ g
  have h_add_smul_ae : F =ᵐ[volume] fun x => c * F₁ x + F₂ x := by
    have h_slice₁ := freeCovarianceℂ_bilinear_slice_integrable m f₁ g
    have h_slice₂ := freeCovarianceℂ_bilinear_slice_integrable m f₂ g
    refine (h_slice₁.and h_slice₂).mono ?_
    intro x hx
    rcases hx with ⟨hf₁x, hf₂x⟩
    have hfun : (fun y => ((c • f₁ + f₂) x) * (freeCovariance d m x y : ℂ) * (g y))
        = fun y => c * (f₁ x * (freeCovariance d m x y : ℂ) * (g y))
            + f₂ x * (freeCovariance d m x y : ℂ) * (g y) := by
      funext y
      have h1 : (c • f₁ + f₂) x = c * f₁ x + f₂ x := rfl
      rw [h1]
      ring
    calc F x
        = ∫ y, ((c • f₁ + f₂) x) * (freeCovariance d m x y : ℂ) * (g y) ∂volume := rfl
      _ = ∫ y, (c * (f₁ x * (freeCovariance d m x y : ℂ) * (g y)) +
            f₂ x * (freeCovariance d m x y : ℂ) * (g y)) ∂volume := by rw [hfun]
      _ = c * F₁ x + F₂ x := by
          have h_const_out :
              ∫ y, c * (f₁ x * (freeCovariance d m x y : ℂ) * (g y)) ∂volume
                = c * ∫ y, (f₁ x * (freeCovariance d m x y : ℂ) * (g y)) ∂volume :=
            MeasureTheory.integral_const_mul c _
          rw [integral_add, h_const_out]
          · exact hf₁x.const_mul c
          · exact hf₂x
  have h_int_eq : ∫ x, F x ∂volume = ∫ x, (c * F₁ x + F₂ x) ∂volume :=
    integral_congr_ae h_add_smul_ae
  have hF₁_smul : Integrable (fun x => c * F₁ x) volume := hF₁.const_mul c
  have h_sum := integral_add hF₁_smul hF₂
  calc ∫ x, F x ∂volume
      = ∫ x, (c * F₁ x + F₂ x) ∂volume := h_int_eq
    _ = (∫ x, c * F₁ x ∂volume) + (∫ x, F₂ x ∂volume) := h_sum
    _ = c * (∫ x, F₁ x ∂volume) + (∫ x, F₂ x ∂volume) := by
        congr 1
        exact MeasureTheory.integral_const_mul _ _

theorem freeCovarianceℂ_bilinear_add_left (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (f₁ f₂ g : SchwartzTestFunctionℂ d) :
    freeCovarianceℂ_bilinear m (f₁ + f₂) g
      = freeCovarianceℂ_bilinear m f₁ g + freeCovarianceℂ_bilinear m f₂ g := by
  have h := freeCovarianceℂ_bilinear_add_smul_left m 1 f₁ f₂ g
  simp only [one_smul, one_mul] at h
  exact h

theorem freeCovarianceℂ_bilinear_smul_left (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (c : ℂ) (f g : SchwartzTestFunctionℂ d) :
    freeCovarianceℂ_bilinear m (c • f) g = c * freeCovarianceℂ_bilinear m f g := by
  have h := freeCovarianceℂ_bilinear_add_smul_left m c f 0 g
  rw [add_zero] at h
  have zero_bilinear : freeCovarianceℂ_bilinear m (0 : SchwartzTestFunctionℂ d) g = 0 := by
    unfold freeCovarianceℂ_bilinear
    have h0 : ∀ x y : SpaceTime d,
        (0 : SchwartzTestFunctionℂ d) x * (freeCovariance d m x y : ℂ) * g y = 0 := by
      intro x y
      have hx : (0 : SchwartzTestFunctionℂ d) x = 0 := rfl
      rw [hx]
      simp only [zero_mul]
    simp_rw [h0]
    rw [integral_zero, integral_zero]
  rw [zero_bilinear, add_zero] at h
  exact h

/-- Symmetry of the bilinear pairing (Fubini plus symmetry of the kernel). -/
theorem freeCovarianceℂ_bilinear_symm (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (f g : SchwartzTestFunctionℂ d) :
    freeCovarianceℂ_bilinear m f g = freeCovarianceℂ_bilinear m g f := by
  unfold freeCovarianceℂ_bilinear
  have h : ∫ x, ∫ y, (f x) * (freeCovariance d m x y : ℂ) * (g y) ∂volume ∂volume
         = ∫ y, ∫ x, (f x) * (freeCovariance d m x y : ℂ) * (g y) ∂volume ∂volume := by
    apply MeasureTheory.integral_integral_swap
    exact freeCovarianceℂ_bilinear_integrable m f g
  rw [h]
  congr 1 with x
  congr 1 with y
  rw [freeCovariance_symm y x]
  ring

theorem freeCovarianceℂ_bilinear_smul_right (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (c : ℂ) (f g : SchwartzTestFunctionℂ d) :
    freeCovarianceℂ_bilinear m f (c • g) = c * freeCovarianceℂ_bilinear m f g := by
  rw [freeCovarianceℂ_bilinear_symm m f (c • g),
    freeCovarianceℂ_bilinear_smul_left m c g f,
    freeCovarianceℂ_bilinear_symm m g f]

theorem freeCovarianceℂ_bilinear_add_right (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (f g₁ g₂ : SchwartzTestFunctionℂ d) :
    freeCovarianceℂ_bilinear m f (g₁ + g₂)
      = freeCovarianceℂ_bilinear m f g₁ + freeCovarianceℂ_bilinear m f g₂ := by
  rw [freeCovarianceℂ_bilinear_symm m f (g₁ + g₂),
    freeCovarianceℂ_bilinear_add_left m g₁ g₂ f,
    freeCovarianceℂ_bilinear_symm m g₁ f, freeCovarianceℂ_bilinear_symm m g₂ f]

end BilinearAlgebra

/-! ### The momentum weight and the weighted `L²` multiplication operator -/

section MomentumWeight

variable {d : ℕ}

/-- The momentum propagator is positive. -/
lemma freePropagatorMom_pos (m : ℝ) [Fact (0 < m)] (k : EuclideanSpace ℝ (Fin d)) :
    0 < freePropagatorMom d m k := by
  unfold OSforGFF.freePropagatorMom
  have hm : (0 : ℝ) < m := Fact.out
  positivity

/-- The momentum propagator is nonnegative. -/
lemma freePropagatorMom_nonneg (m : ℝ) [Fact (0 < m)] (k : EuclideanSpace ℝ (Fin d)) :
    0 ≤ freePropagatorMom d m k :=
  le_of_lt (freePropagatorMom_pos m k)

/-- The square root of the momentum propagator: `1 / √((2π)²‖k‖² + m²)`. -/
noncomputable def freePropagatorMomSqrt (d : ℕ) (m : ℝ) (k : EuclideanSpace ℝ (Fin d)) : ℝ :=
  1 / Real.sqrt ((2 * Real.pi) ^ 2 * ‖k‖ ^ 2 + m ^ 2)

lemma freePropagatorMomSqrt_pos (m : ℝ) [Fact (0 < m)] (k : EuclideanSpace ℝ (Fin d)) :
    0 < freePropagatorMomSqrt d m k := by
  unfold freePropagatorMomSqrt
  have hm : (0 : ℝ) < m := Fact.out
  have h : 0 < Real.sqrt ((2 * Real.pi) ^ 2 * ‖k‖ ^ 2 + m ^ 2) :=
    Real.sqrt_pos.mpr (by positivity)
  positivity

/-- The squared weight is the momentum propagator. -/
lemma freePropagatorMomSqrt_sq (m : ℝ) [Fact (0 < m)] (k : EuclideanSpace ℝ (Fin d)) :
    (freePropagatorMomSqrt d m k) ^ 2 = freePropagatorMom d m k := by
  unfold freePropagatorMomSqrt OSforGFF.freePropagatorMom
  have hm : (0 : ℝ) < m := Fact.out
  rw [div_pow, one_pow, Real.sq_sqrt (by positivity)]

lemma freePropagatorMomSqrt_continuous (m : ℝ) [Fact (0 < m)] :
    Continuous (fun k : EuclideanSpace ℝ (Fin d) => freePropagatorMomSqrt d m k) := by
  unfold freePropagatorMomSqrt
  have hm : (0 : ℝ) < m := Fact.out
  refine continuous_const.div (Real.continuous_sqrt.comp (by fun_prop)) fun k => ?_
  exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

lemma freePropagatorMomSqrt_measurable (m : ℝ) [Fact (0 < m)] :
    Measurable (fun k : EuclideanSpace ℝ (Fin d) => freePropagatorMomSqrt d m k) :=
  (freePropagatorMomSqrt_continuous m).measurable

/-- The weight is pointwise bounded by `1 / m`. -/
lemma freePropagatorMomSqrt_le_inv_mass (m : ℝ) [Fact (0 < m)] :
    ∀ k : EuclideanSpace ℝ (Fin d), freePropagatorMomSqrt d m k ≤ 1 / m := by
  intro k
  have hmpos : 0 < m := Fact.out
  have h1 : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 * ‖k‖ ^ 2 := by positivity
  have hm_sqrt_le : m ≤ Real.sqrt ((2 * Real.pi) ^ 2 * ‖k‖ ^ 2 + m ^ 2) := by
    calc m = Real.sqrt (m ^ 2) := by rw [Real.sqrt_sq hmpos.le]
      _ ≤ Real.sqrt ((2 * Real.pi) ^ 2 * ‖k‖ ^ 2 + m ^ 2) :=
        Real.sqrt_le_sqrt (by linarith)
  unfold freePropagatorMomSqrt
  exact one_div_le_one_div_of_le hmpos hm_sqrt_le

/-- The complexified weight is a.e. bounded by `1 / m`. -/
lemma freePropagatorMomSqrt_bounded_ae (m : ℝ) [Fact (0 < m)] :
    ∀ᵐ k ∂(volume : Measure (EuclideanSpace ℝ (Fin d))),
      ‖(freePropagatorMomSqrt d m k : ℂ)‖ ≤ 1 / m := by
  filter_upwards with k
  rw [Complex.norm_real, Real.norm_of_nonneg (freePropagatorMomSqrt_pos m k).le]
  exact freePropagatorMomSqrt_le_inv_mass m k

/-- Multiplication by the square-root momentum weight as a bounded operator on complex `L²`. -/
noncomputable def freePropagatorMomSqrt_mul_CLM (d : ℕ) (m : ℝ) [Fact (0 < m)] :
    Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  linfty_mul_L2_CLM (fun k => (freePropagatorMomSqrt d m k : ℂ))
    (Complex.continuous_ofReal.measurable.comp (freePropagatorMomSqrt_measurable m)) (1 / m)
    (freePropagatorMomSqrt_bounded_ae m)

/-- The multiplication operator acts pointwise almost everywhere. -/
lemma freePropagatorMomSqrt_mul_CLM_spec (m : ℝ) [Fact (0 < m)]
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin d)))) :
    (freePropagatorMomSqrt_mul_CLM d m f) =ᵐ[volume]
      fun k => (freePropagatorMomSqrt d m k : ℂ) * f k := by
  unfold freePropagatorMomSqrt_mul_CLM
  exact linfty_mul_L2_CLM_spec _ _ _ _ f

/-- Schwartz functions have integrable squared norm. -/
lemma schwartz_normSq_integrable (f : SchwartzTestFunctionℂ d) :
    Integrable (fun k => ‖f k‖ ^ 2) volume := by
  have hf_memLp : MemLp f 2 volume := f.memLp 2 volume
  have hf_meas : AEStronglyMeasurable f volume := hf_memLp.1
  simpa using (memLp_two_iff_integrable_sq_norm hf_meas).1 hf_memLp

end MomentumWeight

/-! ### The centered covariance kernel and its decay -/

/-- The centered position-space covariance kernel `K(z) = C(0, z) = Cprofile ‖z‖`. -/
noncomputable def freeCovarianceKernel (d : ℕ) (m : ℝ) [Fact (0 < m)] [Fact (2 ≤ d)]
    [GFFPropagator d m] (z : SpaceTime d) : ℝ :=
  freeCovariance d m 0 z

section CovarianceKernel

variable {d : ℕ} {m : ℝ} [Fact (0 < m)] [Fact (2 ≤ d)] [GFFPropagator d m]

/-- Translation invariance: `C(x, y) = K(x - y)`. -/
lemma freeCovariance_eq_kernel (x y : SpaceTime d) :
    freeCovariance d m x y = freeCovarianceKernel d m (x - y) := by
  simp only [freeCovariance, freeCovarianceKernel]
  rw [zero_sub, norm_neg]

/-- The centered kernel is continuous away from the origin: it is the radial profile
    `Cprofile ‖z‖`, which agrees with the proper-time integral on `(0, ∞)`. -/
lemma freeCovarianceKernel_continuousOn :
    ContinuousOn (freeCovarianceKernel d m) {z : SpaceTime d | z ≠ 0} := by
  have hm : (0 : ℝ) < m := Fact.out
  have hC : ContinuousOn ((properTimeCovariance d m) ∘ (fun z : SpaceTime d => ‖z‖))
      {z : SpaceTime d | z ≠ 0} :=
    (properTimeCovariance_continuousOn d m hm).comp continuous_norm.continuousOn
      (fun z hz => Set.mem_Ioi.mpr (norm_pos_iff.mpr hz))
  refine hC.congr fun z hz => ?_
  show freeCovarianceKernel d m z = properTimeCovariance d m ‖z‖
  simp only [freeCovarianceKernel, freeCovariance, zero_sub, norm_neg]
  exact GFFPropagator.schwinger_eq ‖z‖ (norm_pos_iff.mpr hz)

/-- The centered kernel is integrable (`GFFPropagator.integrable` in centered form). -/
lemma freeCovarianceKernel_integrable :
    Integrable (freeCovarianceKernel d m) := by
  refine (GFFPropagator.integrable (d := d) (m := m)).congr
    (Filter.Eventually.of_forall fun z => ?_)
  simp only [freeCovarianceKernel, freeCovariance, zero_sub, norm_neg]

/-- Exponential decay of the centered kernel beyond unit radius, with rate `m/2`. -/
lemma freeCovarianceKernel_exp_decay :
    ∃ A : ℝ, 0 < A ∧ ∀ z : SpaceTime d, 1 ≤ ‖z‖ →
      |freeCovarianceKernel d m z| ≤ A * Real.exp (-(m / 2) * ‖z‖) := by
  obtain ⟨A, hA, hbound⟩ := GFFPropagator.decayBound (d := d) (m := m)
  refine ⟨A + 1, by linarith, fun z hz => ?_⟩
  have hK : |freeCovarianceKernel d m z|
      = |GFFPropagator.Cprofile (d := d) (m := m) ‖z‖| := by
    simp only [freeCovarianceKernel, freeCovariance, zero_sub, norm_neg]
  rw [hK]
  refine le_trans (hbound ‖z‖ hz) ?_
  have hexp : (0 : ℝ) ≤ Real.exp (-(m / 2) * ‖z‖) := Real.exp_nonneg _
  nlinarith

/-- Polynomial decay of the centered kernel beyond unit radius: `|K(z)| ≤ C / ‖z‖²`
    (from the exponential decay via `e^{-x} ≤ 2/x²`). -/
lemma freeCovarianceKernel_decay_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ z : SpaceTime d, 1 ≤ ‖z‖ →
      |freeCovarianceKernel d m z| ≤ C / ‖z‖ ^ (2 : ℝ) := by
  have hm : (0 : ℝ) < m := Fact.out
  obtain ⟨A, hA, hbound⟩ := freeCovarianceKernel_exp_decay (d := d) (m := m)
  refine ⟨A * (8 / m ^ 2), by positivity, fun z hz => ?_⟩
  have hz0 : (0 : ℝ) < ‖z‖ := lt_of_lt_of_le one_pos hz
  have hx : (0 : ℝ) < m / 2 * ‖z‖ := by positivity
  have h2 : ((m / 2 * ‖z‖) ^ 2 / 2 : ℝ) ≤ Real.exp (m / 2 * ‖z‖) := by
    have h := Real.pow_div_factorial_le_exp (m / 2 * ‖z‖) hx.le 2
    simpa [Nat.factorial] using h
  have hlow : (0 : ℝ) < (m / 2 * ‖z‖) ^ 2 / 2 := by positivity
  have hexp : Real.exp (-(m / 2) * ‖z‖) ≤ 2 / (m / 2 * ‖z‖) ^ 2 := by
    calc Real.exp (-(m / 2) * ‖z‖)
        = (Real.exp (m / 2 * ‖z‖))⁻¹ := by
          rw [← Real.exp_neg]; congr 1; ring
      _ ≤ ((m / 2 * ‖z‖) ^ 2 / 2)⁻¹ := inv_anti₀ hlow h2
      _ = 2 / (m / 2 * ‖z‖) ^ 2 := by rw [inv_div]
  have hpow : ‖z‖ ^ (2 : ℝ) = ‖z‖ ^ (2 : ℕ) := Real.rpow_two ‖z‖
  calc |freeCovarianceKernel d m z|
      ≤ A * Real.exp (-(m / 2) * ‖z‖) := hbound z hz
    _ ≤ A * (2 / (m / 2 * ‖z‖) ^ 2) := mul_le_mul_of_nonneg_left hexp (le_of_lt hA)
    _ = A * (8 / m ^ 2) / ‖z‖ ^ (2 : ℕ) := by
        field_simp
        ring
    _ = A * (8 / m ^ 2) / ‖z‖ ^ (2 : ℝ) := by rw [hpow]

end CovarianceKernel

end
