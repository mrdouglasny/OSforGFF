/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Data.Complex.Basic

import OSforGFF.Spacetime.Basic
import OSforGFF.Spacetime.PositiveTimeTestFunction
import OSforGFF.Spacetime.DiscreteSymmetry
import OSforGFF.Spacetime.ComplexTestFunction
import OSforGFF.Covariance.ParsevalGeneric

/-!
# Real Covariance Form and Square Root Propagator Embedding

The real covariance bilinear form `C(f,g) = ∫∫ f(x) C(x,y) g(y)` on real test functions,
realized as a squared `L²`-norm: composing the Fourier transform with multiplication by
`√P(k) = 1/√((2π)²‖k‖² + m²)` gives a linear embedding `T : S(ℝ^d) → L²` with

  `C(f, f) = ‖T f‖²_{L²}`  (Parseval bridge + `√P · √P = P`).

This factorization carries the analytic content of the construction: it yields positivity
and continuity of the quadratic form in the Schwartz topology — the hypotheses of the
Minlos theorem, by which the Gaussian measure exists on the space of tempered
distributions (`Measure/Construct.lean`) — and its injectivity (`OS/NonTrivial.lean`)
makes the field non-degenerate.

## Main Results

- `freeCovarianceFormR`: the real covariance bilinear form
- `sqrtPropagatorEmbedding`: the embedding realizing the covariance as a squared norm
- `freeCovarianceFormR_continuous`: continuity of `f ↦ C(f,f)` in the Schwartz topology
- `freeCovarianceFormR_pos`: positivity of the quadratic form
-/

open MeasureTheory Complex Matrix OSforGFF
open scoped Real InnerProductSpace BigOperators ComplexConjugate

noncomputable section

namespace QFT

variable {d : ℕ} [Fact (2 ≤ d)]

/-! ## Real Covariance Form -/

/-- Real covariance bilinear form induced by the free covariance kernel. -/
noncomputable def freeCovarianceFormR (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (f g : SchwartzTestFunction d) : ℝ :=
  ∫ x, ∫ y, (f x) * (freeCovariance d m x y) * (g y) ∂volume ∂volume

theorem freeCovarianceℂ_bilinear_agrees_on_reals
  (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f g : SchwartzTestFunction d) :
    freeCovarianceℂ_bilinear m (toComplex f) (toComplex g)
      = (freeCovarianceFormR m f g : ℂ) := by
  unfold freeCovarianceℂ_bilinear freeCovarianceFormR
  simp only [toComplex_apply]
  have h : ∀ (x y : SpaceTime d),
    ((f x : ℂ)) * ((freeCovariance d m x y : ℂ)) * ((g y : ℂ))
    = (((f x) * (freeCovariance d m x y) * (g y) : ℝ) : ℂ) := by
    intro x y
    simp only [ofReal_mul]
  simp_rw [h]
  have step1 : ∫ x, ∫ y, ((f x * freeCovariance d m x y * g y : ℝ) : ℂ)
             = ∫ x, ((∫ y, f x * freeCovariance d m x y * g y : ℝ) : ℂ) := by
    congr 1 with x
    exact integral_ofReal
  rw [step1]
  exact integral_ofReal

omit [Fact (2 ≤ d)] in
/-- For `c : ℝ` and Schwartz functions over ℂ, ℝ-smul equals ℂ-smul by the canonical coercion. -/
private lemma schwartz_real_smul_eq_complex (c : ℝ) (f : SchwartzMap (SpaceTime d) ℂ) :
    c • f = (c : ℂ) • f := by
  ext x; simp [_root_.smul_apply]

omit [Fact (2 ≤ d)] in
/-- For `c : ℝ` and `Lp ℂ 2`, ℝ-smul equals ℂ-smul by the canonical coercion. -/
private lemma lp_real_smul_eq_complex (c : ℝ) (g : Lp ℂ 2 (volume : Measure (SpaceTime d))) :
    c • g = (c : ℂ) • g := by
  ext1; filter_upwards [Lp.coeFn_smul c g, Lp.coeFn_smul (c : ℂ) g] with x h1 h2
  rw [h1, h2]
  have : c • (g : SpaceTime d → ℂ) x = (c : ℂ) • (g : SpaceTime d → ℂ) x := by
    rw [Complex.real_smul, smul_eq_mul]
  exact this

/-- ℝ-linear view of the complex Fourier transform on Schwartz space.

Built by hand rather than via `restrictScalars`, whose `LinearMap.CompatibleSMul`
instance is not found automatically here. -/
noncomputable def fourierTransformCLM_real :
    SchwartzTestFunctionℂ d →L[ℝ] SchwartzTestFunctionℂ d where
  toLinearMap :=
    { toFun := SchwartzMap.fourierTransformCLM ℂ
      map_add' := fun x y => map_add _ x y
      map_smul' := fun c x => by
        show SchwartzMap.fourierTransformCLM ℂ (c • x) = c • SchwartzMap.fourierTransformCLM ℂ x
        have hcx : c • x = (c : ℂ) • x := schwartz_real_smul_eq_complex c x
        have hmap : SchwartzMap.fourierTransformCLM ℂ ((c : ℂ) • x) =
            (c : ℂ) • SchwartzMap.fourierTransformCLM ℂ x :=
          ContinuousLinearMap.map_smul _ _ _
        rw [hcx, hmap, ← schwartz_real_smul_eq_complex] }
  cont := (SchwartzMap.fourierTransformCLM ℂ).continuous

/-- ℝ-linear view of the Schwartz-to-`L²` embedding. -/
noncomputable def schwartzToL2CLM_real (_m : ℝ) :
    SchwartzTestFunctionℂ d →L[ℝ] Lp ℂ 2 (volume : Measure (SpaceTime d)) where
  toLinearMap :=
    { toFun := SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime d))
      map_add' := fun x y => map_add _ x y
      map_smul' := fun c x => by
        show SchwartzMap.toLpCLM ℂ ℂ 2 volume (c • x) = c • SchwartzMap.toLpCLM ℂ ℂ 2 volume x
        have hcx : c • x = (c : ℂ) • x := schwartz_real_smul_eq_complex c x
        have hmap : SchwartzMap.toLpCLM ℂ ℂ 2 volume ((c : ℂ) • x) =
            (c : ℂ) • SchwartzMap.toLpCLM ℂ ℂ 2 volume x :=
          ContinuousLinearMap.map_smul _ _ _
        rw [hcx, hmap, ← lp_real_smul_eq_complex] }
  cont := (SchwartzMap.toLpCLM ℂ ℂ 2 volume).continuous

/-! ## The Embedding Map -/

/-- The embedding T maps a test function to a weighted function in momentum space.
    Conceptually: T f = FourierTransform(f) * (‖k‖² + m²)^(-1/2). -/
noncomputable def sqrtPropagatorMap (m : ℝ) (f : SchwartzTestFunction d) : SpaceTime d → ℂ :=
  fun k =>
    (SchwartzMap.fourierTransformCLM ℂ (toComplex f)) k
      * freePropagatorMomSqrt d m k

omit [Fact (2 ≤ d)] in
/-- The sqrtPropagatorMap is square-integrable. -/
lemma sqrtPropagatorMap_sq_integrable (m : ℝ) [Fact (0 < m)] (f : SchwartzTestFunction d) :
    Integrable (fun k => ‖sqrtPropagatorMap m f k‖ ^ 2) volume := by
  classical
  set F := SchwartzMap.fourierTransformCLM ℂ (toComplex f)
  have hF_sq : Integrable (fun k => ‖F k‖ ^ 2) volume :=
    schwartz_normSq_integrable F
  have hF_meas : AEStronglyMeasurable F volume := (F.memLp 2 volume).1
  have h_weight_meas : AEStronglyMeasurable (freePropagatorMomSqrt d m) volume :=
    (freePropagatorMomSqrt_measurable (m := m)).aestronglyMeasurable
  have h_map_meas : AEStronglyMeasurable (sqrtPropagatorMap m f) volume := by
    have h_weight_C : AEStronglyMeasurable (fun k => (freePropagatorMomSqrt d m k : ℂ)) volume :=
      Complex.continuous_ofReal.comp_aestronglyMeasurable h_weight_meas
    have : AEStronglyMeasurable (fun k => F k * (freePropagatorMomSqrt d m k : ℂ)) volume :=
      hF_meas.mul h_weight_C
    refine AEStronglyMeasurable.congr this ?_
    filter_upwards with k
    unfold sqrtPropagatorMap
    rfl
  have h_sq_meas : AEStronglyMeasurable (fun k => ‖sqrtPropagatorMap m f k‖ ^ 2) volume :=
    (Continuous.comp_aestronglyMeasurable (by fun_prop) h_map_meas).pow 2
  have h_dom_integrable : Integrable (fun k => (1 / m) ^ 2 * ‖F k‖ ^ 2) volume := by
    have := Integrable.const_mul hF_sq ((1 / m) ^ 2)
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc]
      using this
  have h_dom_pointwise : ∀ᵐ k ∂volume,
      ‖‖sqrtPropagatorMap m f k‖ ^ 2‖ ≤ ‖(1 / m) ^ 2 * ‖F k‖ ^ 2‖ := by
    have hmpos : 0 < m := Fact.out
    refine Filter.Eventually.of_forall ?_
    intro k
    have h_weight_le : (freePropagatorMomSqrt d m k) ^ 2 ≤ (1 / m) ^ 2 := by
      have h_le := freePropagatorMomSqrt_le_inv_mass (m := m) (k := k)
      have h_pos : 0 ≤ freePropagatorMomSqrt d m k := (freePropagatorMomSqrt_pos (m := m) k).le
      gcongr
    have h_nonneg_dom : 0 ≤ (1 / m) ^ 2 * ‖F k‖ ^ 2 := by positivity
    calc ‖‖sqrtPropagatorMap m f k‖ ^ 2‖
        = ‖sqrtPropagatorMap m f k‖ ^ 2 := by
          rw [Real.norm_of_nonneg (sq_nonneg _)]
      _ = ‖F k * (freePropagatorMomSqrt d m k : ℂ)‖ ^ 2 := by
          unfold sqrtPropagatorMap; rfl
      _ = (‖F k‖ * ‖(freePropagatorMomSqrt d m k : ℂ)‖) ^ 2 := by
          rw [norm_mul]
      _ = (‖F k‖ * (freePropagatorMomSqrt d m k)) ^ 2 := by
          congr 1
          rw [Complex.norm_real, Real.norm_of_nonneg (freePropagatorMomSqrt_pos (m := m) k).le]
      _ = ‖F k‖ ^ 2 * (freePropagatorMomSqrt d m k) ^ 2 := by
          rw [mul_pow]
      _ ≤ ‖F k‖ ^ 2 * (1 / m) ^ 2 := by
          gcongr
      _ = (1 / m) ^ 2 * ‖F k‖ ^ 2 := by ring
      _ = ‖(1 / m) ^ 2 * ‖F k‖ ^ 2‖ := by
          rw [Real.norm_of_nonneg h_nonneg_dom]
  exact h_dom_integrable.mono h_sq_meas h_dom_pointwise

omit [Fact (2 ≤ d)] in
/-- The weighted Fourier representative lies in L². -/
lemma sqrtPropagatorMap_memLp (m : ℝ) [Fact (0 < m)] (f : SchwartzTestFunction d) :
    MemLp (sqrtPropagatorMap m f) 2 volume := by
  classical
  set F := SchwartzMap.fourierTransformCLM ℂ (toComplex f)
  have hF_meas : AEStronglyMeasurable F volume := (F.memLp 2 volume).1
  have h_weight_meas : AEStronglyMeasurable (freePropagatorMomSqrt d m) volume :=
    (freePropagatorMomSqrt_measurable (m := m)).aestronglyMeasurable
  have h_weight_C : AEStronglyMeasurable (fun k => (freePropagatorMomSqrt d m k : ℂ)) volume :=
    Complex.continuous_ofReal.comp_aestronglyMeasurable h_weight_meas
  have h_meas_mul : AEStronglyMeasurable (fun k => F k * (freePropagatorMomSqrt d m k : ℂ)) volume :=
    hF_meas.mul h_weight_C
  have h_meas : AEStronglyMeasurable (sqrtPropagatorMap m f) volume :=
    h_meas_mul.congr <| Filter.Eventually.of_forall fun k => by
      unfold sqrtPropagatorMap
      rfl
  have h_sq := sqrtPropagatorMap_sq_integrable (m := m) (f := f)
  exact (memLp_two_iff_integrable_sq_norm h_meas).2 h_sq

/-- The squared L² norm of the mapped function. -/
noncomputable def sqrtPropagatorMap_norm_sq (m : ℝ) (f : SchwartzTestFunction d) : ℝ :=
  ∫ k, ‖sqrtPropagatorMap m f k‖ ^ 2 ∂volume

omit [Fact (2 ≤ d)] in
/-- The map is linear in f (additive). -/
lemma sqrtPropagatorMap_linear_add (m : ℝ) [Fact (0 < m)] (f g : SchwartzTestFunction d) :
    sqrtPropagatorMap m (f + g) = sqrtPropagatorMap m f + sqrtPropagatorMap m g := by
  ext k
  unfold sqrtPropagatorMap
  have hadd : toComplex (f + g) = toComplex f + toComplex g := toComplex_add f g
  have hmap : SchwartzMap.fourierTransformCLM ℂ (toComplex f + toComplex g) =
      SchwartzMap.fourierTransformCLM ℂ (toComplex f) +
        SchwartzMap.fourierTransformCLM ℂ (toComplex g) :=
    map_add _ _ _
  simp only [hadd, hmap, _root_.add_apply, Pi.add_apply, add_mul]

omit [Fact (2 ≤ d)] in
/-- The map is ℝ-linear (scalar multiplication). -/
lemma sqrtPropagatorMap_linear_smul (m : ℝ) [Fact (0 < m)] (c : ℝ) (f : SchwartzTestFunction d) :
    sqrtPropagatorMap m (c • f) = c • sqrtPropagatorMap m f := by
  ext k
  unfold sqrtPropagatorMap
  have hsmul : toComplex (c • f) = (c : ℂ) • toComplex f := toComplex_smul c f
  have hmap : SchwartzMap.fourierTransformCLM ℂ ((c : ℂ) • toComplex f) =
      (c : ℂ) • SchwartzMap.fourierTransformCLM ℂ (toComplex f) :=
    ContinuousLinearMap.map_smul _ _ _
  simp only [hsmul, hmap, _root_.smul_apply, smul_eq_mul, Pi.smul_apply, Complex.real_smul]
  ring

/-! ## Connection to Covariance -/

omit [Fact (2 ≤ d)] in
/-- For real test functions, the star (conjugation) of toComplex is the identity. -/
lemma toComplex_star (f : SchwartzTestFunction d) (x : SpaceTime d) :
    starRingEnd ℂ (toComplex f x) = toComplex f x := by
  simp [toComplex_apply]

/-- For real test functions, freeCovarianceℂ agrees with freeCovarianceℂ_bilinear. -/
lemma freeCovarianceℂ_eq_bilinear_on_reals (m : ℝ) [Fact (0 < m)] [GFFPropagator d m]
    (f g : SchwartzTestFunction d) :
    freeCovarianceℂ m (toComplex f) (toComplex g)
      = freeCovarianceℂ_bilinear m (toComplex f) (toComplex g) := by
  unfold freeCovarianceℂ freeCovarianceℂ_bilinear
  congr 1 with x
  congr 1 with y
  rw [toComplex_star]

/-- Key lemma: The squared norm equals the covariance form. -/
lemma sqrtPropagatorMap_norm_eq_covariance (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : SchwartzTestFunction d) :
    sqrtPropagatorMap_norm_sq m f = freeCovarianceFormR m f f := by
  classical
  set F := SchwartzMap.fourierTransformCLM ℂ (toComplex f)
  -- The squared norm of sqrtPropagatorMap equals |F|² * weight_mathlib
  have h_ae :
      (fun k => ‖sqrtPropagatorMap m f k‖ ^ 2)
        =ᵐ[volume] fun k => ‖F k‖ ^ 2 * freePropagatorMom d m k := by
    refine Filter.Eventually.of_forall ?_
    intro k
    have h_nonneg : 0 ≤ freePropagatorMomSqrt d m k := (freePropagatorMomSqrt_pos (m := m) k).le
    have h_abs : ‖(freePropagatorMomSqrt d m k : ℂ)‖ = freePropagatorMomSqrt d m k := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h_nonneg]
    have h_norm : ‖sqrtPropagatorMap m f k‖ = ‖F k‖ * freePropagatorMomSqrt d m k := by
      calc
        ‖sqrtPropagatorMap m f k‖ = ‖F k * freePropagatorMomSqrt d m k‖ := rfl
        _ = ‖F k‖ * ‖(freePropagatorMomSqrt d m k : ℂ)‖ := by simp
        _ = ‖F k‖ * freePropagatorMomSqrt d m k := by
          have h := congrArg (fun t : ℝ => ‖F k‖ * t) h_abs
          simpa using h
    have h_sq : ‖sqrtPropagatorMap m f k‖ ^ 2
        = ‖F k‖ ^ 2 * (freePropagatorMomSqrt d m k) ^ 2 := by
      simp [pow_two, h_norm, mul_comm, mul_left_comm, mul_assoc]
    have h_sq_goal : ‖sqrtPropagatorMap m f k‖ ^ 2
        = ‖F k‖ ^ 2 * freePropagatorMom d m k := by
      simpa [F, freePropagatorMomSqrt_sq] using h_sq
    exact h_sq_goal
  have h_norm_int :
      sqrtPropagatorMap_norm_sq m f
        = ∫ k, ‖F k‖ ^ 2 * freePropagatorMom d m k ∂volume := by
    simpa [sqrtPropagatorMap_norm_sq]
      using MeasureTheory.integral_congr_ae h_ae
  -- freePropagatorMom d = freePropagatorMom d by definition
  have h_integral_eq :
      ∫ k, ‖F k‖ ^ 2 * freePropagatorMom d m k ∂volume
        = (freeCovarianceℂ m (toComplex f) (toComplex f)).re := by
    -- freePropagatorMom d = freePropagatorMom d
    exact (parseval_covariance_schwartz (m := m) (f := toComplex f)).symm
  have h_real_cov :
      (freeCovarianceℂ m (toComplex f) (toComplex f)).re = freeCovarianceFormR m f f := by
    have h_complex :
        freeCovarianceℂ m (toComplex f) (toComplex f)
          = (freeCovarianceFormR m f f : ℂ) := by
      calc
        freeCovarianceℂ m (toComplex f) (toComplex f)
            = freeCovarianceℂ_bilinear m (toComplex f) (toComplex f) :=
                freeCovarianceℂ_eq_bilinear_on_reals m f f
        _ = (freeCovarianceFormR m f f : ℂ) :=
                freeCovarianceℂ_bilinear_agrees_on_reals m f f
    have := congrArg (fun z : ℂ => z.re) h_complex
    simpa using this
  calc
    sqrtPropagatorMap_norm_sq m f
        = ∫ k, ‖F k‖ ^ 2 * freePropagatorMom d m k ∂volume := h_norm_int
    _ = (freeCovarianceℂ m (toComplex f) (toComplex f)).re := h_integral_eq
    _ = freeCovarianceFormR m f f := h_real_cov

/-! ## The Proof of sqrtPropagatorEmbedding -/

/-- The target Hilbert space: L²(SpaceTime d, Lebesgue) with complex values. -/
abbrev TargetHilbertSpace (d : ℕ) (_m : ℝ) : Type :=
  Lp (E := ℂ) 2 (volume : Measure (SpaceTime d))

/-- The linear map T: SchwartzTestFunction d → L². -/
noncomputable def embeddingMap (m : ℝ) [Fact (0 < m)] :
    SchwartzTestFunction d →ₗ[ℝ] TargetHilbertSpace d m :=
  { toFun := fun f =>
      (sqrtPropagatorMap_memLp (m := m) (f := f)).toLp (sqrtPropagatorMap m f)
    map_add' := by
      intro f g
      have hf := sqrtPropagatorMap_memLp (m := m) (f := f)
      have hg := sqrtPropagatorMap_memLp (m := m) (f := g)
      have hfg := sqrtPropagatorMap_memLp (m := m) (f := f + g)
      have h_linear : sqrtPropagatorMap m (f + g) =ᵐ[volume] sqrtPropagatorMap m f + sqrtPropagatorMap m g := by
        filter_upwards with k
        exact sqrtPropagatorMap_linear_add m f g ▸ rfl
      rw [← MeasureTheory.MemLp.toLp_add hf hg]
      exact MeasureTheory.MemLp.toLp_congr hfg (hf.add hg) h_linear
    map_smul' := by
      intro c f
      have hf := sqrtPropagatorMap_memLp (m := m) (f := f)
      have hcf := sqrtPropagatorMap_memLp (m := m) (f := c • f)
      have h_linear : sqrtPropagatorMap m (c • f) =ᵐ[volume] c • sqrtPropagatorMap m f := by
        filter_upwards with k
        exact sqrtPropagatorMap_linear_smul m c f ▸ rfl
      have : hcf.toLp (sqrtPropagatorMap m (c • f)) = (hf.const_smul c).toLp (c • sqrtPropagatorMap m f) :=
        MeasureTheory.MemLp.toLp_congr hcf (hf.const_smul c) h_linear
      rw [this]
      exact MeasureTheory.MemLp.toLp_const_smul c hf }

/-- ℝ-linear view of the Lp multiplication CLM (avoiding `restrictScalars`). -/
private noncomputable def freePropagatorMomSqrt_mul_CLM_real (m : ℝ) [Fact (0 < m)] :
    Lp ℂ 2 (volume : Measure (SpaceTime d)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (SpaceTime d)) where
  toLinearMap :=
    { toFun := freePropagatorMomSqrt_mul_CLM d m
      map_add' := fun x y => map_add _ x y
      map_smul' := fun c x => by
        show freePropagatorMomSqrt_mul_CLM d m (c • x)
            = c • freePropagatorMomSqrt_mul_CLM d m x
        have hcx : c • x = (c : ℂ) • x := lp_real_smul_eq_complex c x
        have hmap : freePropagatorMomSqrt_mul_CLM d m ((c : ℂ) • x) =
            (c : ℂ) • freePropagatorMomSqrt_mul_CLM d m x :=
          ContinuousLinearMap.map_smul _ _ _
        rw [hcx, hmap, ← lp_real_smul_eq_complex] }
  cont := (freePropagatorMomSqrt_mul_CLM d m).continuous

/-- Continuous linear map obtained by composing the proven building blocks. -/
noncomputable def embeddingMapCLM (m : ℝ) [Fact (0 < m)] :
    SchwartzTestFunction d →L[ℝ] Lp ℂ 2 (volume : Measure (SpaceTime d)) :=
  ((freePropagatorMomSqrt_mul_CLM_real m).comp (schwartzToL2CLM_real m)).comp
    ((fourierTransformCLM_real).comp toComplexCLM)

omit [Fact (2 ≤ d)] in
lemma embeddingMapCLM_apply (m : ℝ) [Fact (0 < m)] (f : SchwartzTestFunction d) :
    embeddingMapCLM m f = embeddingMap m f := by
  classical
  set g := SchwartzMap.fourierTransformCLM ℂ (toComplex f) with hg
  set A := (SchwartzMap.toLpCLM ℂ ℂ 2 (volume : Measure (SpaceTime d))) g with hA
  have h_eval : embeddingMapCLM m f = (freePropagatorMomSqrt_mul_CLM d m) A := by
    rfl
  have h_mul := freePropagatorMomSqrt_mul_CLM_spec (m := m) A
  have h_mul' : embeddingMapCLM m f =ᵐ[volume]
      fun k => (freePropagatorMomSqrt d m k : ℂ) * A k := by
    simpa [h_eval]
  have h_A : (fun k => A k) =ᵐ[volume] fun k => g k := by
    simpa [A, hA]
      using g.coeFn_toLp 2 (volume : Measure (SpaceTime d))
  have h_weight : (fun k => (freePropagatorMomSqrt d m k : ℂ) * A k)
      =ᵐ[volume] fun k => (freePropagatorMomSqrt d m k : ℂ) * g k := by
    refine h_A.mono ?_
    intro k hk
    simp [hk]
  have h_mul'' : embeddingMapCLM m f =ᵐ[volume]
      fun k => (freePropagatorMomSqrt d m k : ℂ) * g k :=
    h_mul'.trans h_weight
  have h_sqrt : (fun k => (freePropagatorMomSqrt d m k : ℂ) * g k)
      =ᵐ[volume] sqrtPropagatorMap m f := by
    refine Filter.Eventually.of_forall ?_
    intro k
    simp [sqrtPropagatorMap, g, mul_comm]
  have h_mem := sqrtPropagatorMap_memLp (m := m) (f := f)
  have h_lp : embeddingMap m f =ᵐ[volume] sqrtPropagatorMap m f := by
    simpa [embeddingMap] using h_mem.coeFn_toLp
  have h_ae : embeddingMapCLM m f =ᵐ[volume] embeddingMap m f :=
    (h_mul''.trans h_sqrt).trans h_lp.symm
  exact Lp.ext_iff.mpr h_ae

/-- Existence of a linear embedding realizing the free covariance as a squared norm.
    The target space H is an inner product space (L² is a Hilbert space).
    Note: InnerProductSpace ℝ H implies NormedSpace ℝ H via InnerProductSpace.toNormedSpace. -/
theorem sqrtPropagatorEmbedding (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H)
    (T : SchwartzTestFunction d →ₗ[ℝ] H),
    ∀ f : SchwartzTestFunction d, freeCovarianceFormR m f f = ‖T f‖^2 := by
  refine ⟨TargetHilbertSpace d m, inferInstance, inferInstance, embeddingMap m, ?_⟩
  intro f
  rw [← sqrtPropagatorMap_norm_eq_covariance]
  unfold sqrtPropagatorMap_norm_sq
  symm
  have h_memLp := sqrtPropagatorMap_memLp (m := m) (f := f)
  show ‖embeddingMap m f‖ ^ 2 = ∫ (k : SpaceTime d), ‖sqrtPropagatorMap m f k‖ ^ 2
  change ‖h_memLp.toLp (sqrtPropagatorMap m f)‖ ^ 2 = _
  have h_norm : ‖h_memLp.toLp (sqrtPropagatorMap m f)‖ = ENNReal.toReal (eLpNorm (sqrtPropagatorMap m f) 2 volume) :=
    MeasureTheory.Lp.norm_toLp (sqrtPropagatorMap m f) h_memLp
  rw [h_norm]
  have h_integrable := sqrtPropagatorMap_sq_integrable (m := m) (f := f)
  have h_two_ne : (2 : NNReal) ≠ 0 := by norm_num
  calc (ENNReal.toReal (eLpNorm (sqrtPropagatorMap m f) 2 volume)) ^ 2
      = ENNReal.toReal ((eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ 2) := by
          symm; exact ENNReal.toReal_pow _ 2
    _ = ENNReal.toReal (∫⁻ k, (‖sqrtPropagatorMap m f k‖₊ : ENNReal) ^ 2) := by
          congr 1
          have h_eq := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral (f := sqrtPropagatorMap m f) (p := 2) (μ := volume) h_two_ne
          simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at h_eq
          have h_pow_cast : (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℕ) = (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℝ) := by
            simp [pow_two]
          calc (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℕ)
              = (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℝ) := h_pow_cast
            _ = ∫⁻ (x : SpaceTime d), ‖sqrtPropagatorMap m f x‖ₑ ^ 2 := h_eq
            _ = ∫⁻ (k : SpaceTime d), (‖sqrtPropagatorMap m f k‖₊ : ENNReal) ^ 2 := by
              refine lintegral_congr_ae ?_; filter_upwards with k; simp only [enorm]; norm_cast
    _ = ∫ k, ‖sqrtPropagatorMap m f k‖ ^ 2 := by
          have h_ae_meas := h_integrable.aestronglyMeasurable
          have h_nonneg : ∀ᵐ k ∂volume, 0 ≤ ‖sqrtPropagatorMap m f k‖ ^ 2 :=
            Filter.Eventually.of_forall fun k => sq_nonneg _
          rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nonneg h_ae_meas]
          congr 1
          refine lintegral_congr_ae ?_
          filter_upwards with k
          rw [ENNReal.ofReal_pow (norm_nonneg _)]
          simp only [pow_two]
          conv_rhs => arg 1; rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
          conv_rhs => arg 2; rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

/-! ## Auxiliary Lemmas for Continuity -/

omit [Fact (2 ≤ d)] in
/-- Squared L² norm of the embedded function in terms of the pointwise integral. -/
lemma embeddingMap_norm_sq (m : ℝ) [Fact (0 < m)] (f : SchwartzTestFunction d) :
    ‖embeddingMap m f‖ ^ 2 = ∫ (k : SpaceTime d), ‖sqrtPropagatorMap m f k‖ ^ 2 ∂volume := by
  have h_memLp := sqrtPropagatorMap_memLp (m := m) (f := f)
  change ‖h_memLp.toLp (sqrtPropagatorMap m f)‖ ^ 2 = _
  have h_norm : ‖h_memLp.toLp (sqrtPropagatorMap m f)‖
      = ENNReal.toReal (eLpNorm (sqrtPropagatorMap m f) 2 volume) :=
    MeasureTheory.Lp.norm_toLp (sqrtPropagatorMap m f) h_memLp
  rw [h_norm]
  have h_integrable := sqrtPropagatorMap_sq_integrable (m := m) (f := f)
  have h_two_ne : (2 : NNReal) ≠ 0 := by norm_num
  calc
    (ENNReal.toReal (eLpNorm (sqrtPropagatorMap m f) 2 volume)) ^ 2
        = ENNReal.toReal ((eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ 2) := by
            symm; exact ENNReal.toReal_pow _ 2
    _ = ENNReal.toReal (∫⁻ k, (‖sqrtPropagatorMap m f k‖₊ : ENNReal) ^ 2) := by
            congr 1
            have h_eq := MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral
              (f := sqrtPropagatorMap m f) (p := 2) (μ := volume) h_two_ne
            simp only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at h_eq
            have h_pow_cast : (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℕ)
                = (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℝ) := by
              simp [pow_two]
            calc (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℕ)
                = (eLpNorm (sqrtPropagatorMap m f) 2 volume) ^ (2 : ℝ) := h_pow_cast
              _ = ∫⁻ (x : SpaceTime d), ‖sqrtPropagatorMap m f x‖ₑ ^ 2 := h_eq
              _ = ∫⁻ (k : SpaceTime d), (‖sqrtPropagatorMap m f k‖₊ : ENNReal) ^ 2 := by
                refine lintegral_congr_ae ?_
                filter_upwards with k
                simp only [enorm]
                norm_cast
    _ = ∫ k, ‖sqrtPropagatorMap m f k‖ ^ 2 := by
            have h_ae_meas := h_integrable.aestronglyMeasurable
            have h_nonneg : ∀ᵐ k ∂volume, 0 ≤ ‖sqrtPropagatorMap m f k‖ ^ 2 :=
              Filter.Eventually.of_forall fun k => sq_nonneg _
            rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae h_nonneg h_ae_meas]
            congr 1
            refine lintegral_congr_ae ?_
            filter_upwards with k
            rw [ENNReal.ofReal_pow (norm_nonneg _)]
            simp only [pow_two]
            conv_rhs => arg 1; rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]
            conv_rhs => arg 2; rw [← coe_nnnorm, ENNReal.ofReal_coe_nnreal]

lemma freeCovarianceFormR_eq_normSq (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : SchwartzTestFunction d) :
    freeCovarianceFormR m f f = ‖embeddingMap m f‖ ^ 2 := by
  have h_cov := sqrtPropagatorMap_norm_eq_covariance (m := m) (f := f)
  have h_norm := embeddingMap_norm_sq (m := m) (f := f)
  simpa [sqrtPropagatorMap_norm_sq, h_norm] using h_cov.symm

omit [Fact (2 ≤ d)] in
/-- The embedding map SchwartzTestFunction d → L² is continuous. -/
lemma embeddingMap_continuous (m : ℝ) [Fact (0 < m)] :
    Continuous (embeddingMap (d := d) m) := by
  classical
  have h := (embeddingMapCLM (d := d) (m := m)).continuous
  have h_fun_eq : (fun f : SchwartzTestFunction d => embeddingMapCLM m f)
      = (fun f => embeddingMap m f) := by
    funext f
    simp [embeddingMapCLM_apply]
  exact (continuous_congr (congrFun h_fun_eq)).mp h

/-- Continuity of the real covariance quadratic form f ↦ C(f,f). -/
theorem freeCovarianceFormR_continuous (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    Continuous (fun f : SchwartzTestFunction d => freeCovarianceFormR m f f) := by
  have h_eq : (fun f : SchwartzTestFunction d => freeCovarianceFormR m f f)
      = (fun f => ‖embeddingMap m f‖ ^ 2) := by
    ext f
    exact freeCovarianceFormR_eq_normSq (m := m) (f := f)
  rw [h_eq]
  have h_cont_map : Continuous (embeddingMap (d := d) m) := embeddingMap_continuous (m := m)
  have h_cont_norm : Continuous (fun f => ‖embeddingMap m f‖) := Continuous.norm h_cont_map
  exact Continuous.pow h_cont_norm 2

/-! ## Positivity and Other Properties -/

/-- Positivity of the real covariance quadratic form. -/
theorem freeCovarianceFormR_pos (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] :
    ∀ f : SchwartzTestFunction d, 0 ≤ freeCovarianceFormR m f f := by
  intro f
  have h1 : freeCovarianceℂ_bilinear m (toComplex f) (toComplex f) = (freeCovarianceFormR m f f : ℂ) :=
    freeCovarianceℂ_bilinear_agrees_on_reals m f f
  have h2 : freeCovarianceℂ m (toComplex f) (toComplex f)
              = freeCovarianceℂ_bilinear m (toComplex f) (toComplex f) :=
    freeCovarianceℂ_eq_bilinear_on_reals m f f
  have h3 : 0 ≤ (freeCovarianceℂ m (toComplex f) (toComplex f)).re :=
    freeCovarianceℂ_positive (m := m) (toComplex f)
  rw [h2, h1] at h3
  simpa using h3

/-- Symmetry of the real covariance bilinear form. -/
theorem freeCovarianceFormR_symm (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f g : SchwartzTestFunction d) :
    freeCovarianceFormR m f g = freeCovarianceFormR m g f := by
  apply Complex.ofReal_injective
  calc (freeCovarianceFormR m f g : ℂ)
      = freeCovarianceℂ_bilinear m (toComplex f) (toComplex g) := by
          rw [← freeCovarianceℂ_bilinear_agrees_on_reals m f g]
    _ = freeCovarianceℂ_bilinear m (toComplex g) (toComplex f) := by
          rw [freeCovarianceℂ_bilinear_symm m (toComplex f) (toComplex g)]
    _ = (freeCovarianceFormR m g f : ℂ) := by
          rw [freeCovarianceℂ_bilinear_agrees_on_reals m g f]

/-- Linearity in the first argument of the real covariance bilinear form. -/
lemma freeCovarianceFormR_add_left (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f₁ f₂ g : SchwartzTestFunction d) :
    freeCovarianceFormR m (f₁ + f₂) g = freeCovarianceFormR m f₁ g + freeCovarianceFormR m f₂ g := by
  apply Complex.ofReal_injective
  have h :=
    freeCovarianceℂ_bilinear_add_left m (toComplex f₁) (toComplex f₂) (toComplex g)
  have hL :
      (freeCovarianceFormR m (f₁ + f₂) g : ℂ)
        = freeCovarianceℂ_bilinear m (toComplex f₁ + toComplex f₂) (toComplex g) := by
    simpa [toComplex_add]
      using (freeCovarianceℂ_bilinear_agrees_on_reals m (f₁ + f₂) g).symm
  have h' :
      (freeCovarianceFormR m (f₁ + f₂) g : ℂ)
        = (freeCovarianceFormR m f₁ g : ℂ) + (freeCovarianceFormR m f₂ g : ℂ) := by
    calc
      (freeCovarianceFormR m (f₁ + f₂) g : ℂ)
          = freeCovarianceℂ_bilinear m (toComplex f₁ + toComplex f₂) (toComplex g) := hL
      _ = freeCovarianceℂ_bilinear m (toComplex f₁) (toComplex g)
            + freeCovarianceℂ_bilinear m (toComplex f₂) (toComplex g) := h
      _ = (freeCovarianceFormR m f₁ g : ℂ) + (freeCovarianceFormR m f₂ g : ℂ) := by
            rw [freeCovarianceℂ_bilinear_agrees_on_reals m f₁ g,
                freeCovarianceℂ_bilinear_agrees_on_reals m f₂ g]
  simpa [Complex.ofReal_add] using h'

/-- Scalar multiplication in the first argument of the real covariance bilinear form. -/
lemma freeCovarianceFormR_smul_left (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (c : ℝ) (f g : SchwartzTestFunction d) :
    freeCovarianceFormR m (c • f) g = c * freeCovarianceFormR m f g := by
  apply Complex.ofReal_injective
  have h :=
    freeCovarianceℂ_bilinear_smul_left m (c : ℂ) (toComplex f) (toComplex g)
  have hL :
      (freeCovarianceFormR m (c • f) g : ℂ)
        = freeCovarianceℂ_bilinear m ((c : ℂ) • toComplex f) (toComplex g) := by
    simpa [toComplex_apply]
      using (freeCovarianceℂ_bilinear_agrees_on_reals m (c • f) g).symm
  have hR :
      (freeCovarianceFormR m f g : ℂ)
        = freeCovarianceℂ_bilinear m (toComplex f) (toComplex g) :=
    (freeCovarianceℂ_bilinear_agrees_on_reals m f g).symm
  have h' :
      (freeCovarianceFormR m (c • f) g : ℂ)
        = (c : ℂ) * (freeCovarianceFormR m f g : ℂ) := by
    calc
      (freeCovarianceFormR m (c • f) g : ℂ)
          = freeCovarianceℂ_bilinear m ((c : ℂ) • toComplex f) (toComplex g) := hL
      _ = (c : ℂ) * freeCovarianceℂ_bilinear m (toComplex f) (toComplex g) := h
      _ = (c : ℂ) * (freeCovarianceFormR m f g : ℂ) := by
            rw [hR]
  simpa [Complex.ofReal_mul] using h'

/-- Addition in the second argument of the real covariance bilinear form. -/
lemma freeCovarianceFormR_add_right (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f g₁ g₂ : SchwartzTestFunction d) :
    freeCovarianceFormR m f (g₁ + g₂) = freeCovarianceFormR m f g₁ + freeCovarianceFormR m f g₂ := by
  apply Complex.ofReal_injective
  have h :=
    freeCovarianceℂ_bilinear_add_right m (toComplex f) (toComplex g₁) (toComplex g₂)
  have hL :
      (freeCovarianceFormR m f (g₁ + g₂) : ℂ)
        = freeCovarianceℂ_bilinear m (toComplex f) (toComplex g₁ + toComplex g₂) := by
    simpa [toComplex_add]
      using (freeCovarianceℂ_bilinear_agrees_on_reals m f (g₁ + g₂)).symm
  have h' :
      (freeCovarianceFormR m f (g₁ + g₂) : ℂ)
        = (freeCovarianceFormR m f g₁ : ℂ) + (freeCovarianceFormR m f g₂ : ℂ) := by
    calc
      (freeCovarianceFormR m f (g₁ + g₂) : ℂ)
          = freeCovarianceℂ_bilinear m (toComplex f) (toComplex g₁ + toComplex g₂) := hL
      _ = freeCovarianceℂ_bilinear m (toComplex f) (toComplex g₁)
            + freeCovarianceℂ_bilinear m (toComplex f) (toComplex g₂) := h
      _ = (freeCovarianceFormR m f g₁ : ℂ) + (freeCovarianceFormR m f g₂ : ℂ) := by
            rw [freeCovarianceℂ_bilinear_agrees_on_reals m f g₁,
                freeCovarianceℂ_bilinear_agrees_on_reals m f g₂]
  simpa [Complex.ofReal_add] using h'

/-- Scalar multiplication in the second argument of the real covariance bilinear form. -/
lemma freeCovarianceFormR_smul_right (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (c : ℝ) (f g : SchwartzTestFunction d) :
    freeCovarianceFormR m f (c • g) = c * freeCovarianceFormR m f g := by
  apply Complex.ofReal_injective
  have h :=
    freeCovarianceℂ_bilinear_smul_right m (c : ℂ) (toComplex f) (toComplex g)
  have hL :
    (freeCovarianceFormR m f (c • g) : ℂ)
        = freeCovarianceℂ_bilinear m (toComplex f) ((c : ℂ) • toComplex g) := by
    simpa [toComplex_apply]
      using (freeCovarianceℂ_bilinear_agrees_on_reals m f (c • g)).symm
  have hR :
      (freeCovarianceFormR m f g : ℂ)
        = freeCovarianceℂ_bilinear m (toComplex f) (toComplex g) :=
    (freeCovarianceℂ_bilinear_agrees_on_reals m f g).symm
  have h' :
      (freeCovarianceFormR m f (c • g) : ℂ)
        = (c : ℂ) * (freeCovarianceFormR m f g : ℂ) := by
    calc
      (freeCovarianceFormR m f (c • g) : ℂ)
          = freeCovarianceℂ_bilinear m (toComplex f) ((c : ℂ) • toComplex g) := hL
      _ = (c : ℂ) * freeCovarianceℂ_bilinear m (toComplex f) (toComplex g) := h
      _ = (c : ℂ) * (freeCovarianceFormR m f g : ℂ) := by
            rw [hR]
  simpa [Complex.ofReal_mul] using h'

/-- Zero in the first argument gives zero. -/
lemma freeCovarianceFormR_zero_left (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (g : SchwartzTestFunction d) :
    freeCovarianceFormR m 0 g = 0 := by
  have h := freeCovarianceFormR_smul_left m (0 : ℝ) 0 g
  simp only [zero_smul] at h
  rw [h]
  simp only [zero_mul]

/-- Zero in the second argument gives zero. -/
lemma freeCovarianceFormR_zero_right (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f : SchwartzTestFunction d) :
    freeCovarianceFormR m f 0 = 0 := by
  rw [freeCovarianceFormR_symm]
  exact freeCovarianceFormR_zero_left m f

lemma freeCovarianceFormR_reflection_invariant
    (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f g : SchwartzTestFunction d) :
    freeCovarianceFormR m (QFT.compTimeReflectionReal f)
      (QFT.compTimeReflectionReal g) = freeCovarianceFormR m f g := by
  classical
  set fc : SchwartzTestFunctionℂ d := toComplex f
  set gc : SchwartzTestFunctionℂ d := toComplex g
  have h_comp_invol (h : SchwartzTestFunctionℂ d) :
      QFT.compTimeReflection (QFT.compTimeReflection h) = h := by
    ext x
    simp only [QFT.compTimeReflection, SchwartzMap.compCLM_apply, Function.comp_apply]
    congr 1
    exact QFT.timeReflectionLE.right_inv x
  have h_toComplex_comp (h : SchwartzTestFunction d) :
      toComplex (QFT.compTimeReflectionReal h)
        = QFT.compTimeReflection (toComplex h) := by
    ext x
    simp [toComplex_apply, QFT.compTimeReflectionReal, QFT.compTimeReflection,
      QFT.timeReflectionCLM]
  have h_integrable :
      Integrable
        (fun p : SpaceTime d × SpaceTime d =>
          (QFT.compTimeReflection fc) p.1
            * (freeCovariance d m p.1 p.2 : ℂ)
            * (QFT.compTimeReflection gc) p.2)
        (volume.prod volume) :=
    freeCovarianceℂ_bilinear_integrable (m := m)
      (f := QFT.compTimeReflection fc) (g := QFT.compTimeReflection gc)
  have h_double :=
    double_integral_timeReflection_covariance (m := m)
      (f := fc) (g := QFT.compTimeReflection gc) h_integrable
  have h_complex :
      freeCovarianceℂ_bilinear m (QFT.compTimeReflection fc) (QFT.compTimeReflection gc)
        = freeCovarianceℂ_bilinear m fc gc := by
    have h_double' := h_double
    simp_rw [covariance_timeReflection_invariant m] at h_double'
    have h_double'' :
        ∫ x, ∫ y,
            (QFT.compTimeReflection fc) x * (freeCovariance d m x y : ℂ)
              * (QFT.compTimeReflection gc) y ∂volume ∂volume
          =
        ∫ x, ∫ y,
            fc x * (freeCovariance d m x y : ℂ) * gc y ∂volume ∂volume := by
      calc
        ∫ x, ∫ y,
            (QFT.compTimeReflection fc) x * (freeCovariance d m x y : ℂ)
              * (QFT.compTimeReflection gc) y ∂volume ∂volume
          = ∫ x, ∫ y,
              fc x * (freeCovariance d m x y : ℂ)
                * (QFT.compTimeReflection (QFT.compTimeReflection gc)) y ∂volume ∂volume := h_double'
        _ = ∫ x, ∫ y,
                fc x * (freeCovariance d m x y : ℂ) * gc y ∂volume ∂volume := by
              exact
                congrArg
                  (fun h : SchwartzTestFunctionℂ d =>
                    ∫ x, ∫ y,
                        fc x * (freeCovariance d m x y : ℂ) * h y ∂volume ∂volume)
                  (h_comp_invol gc)
    unfold freeCovarianceℂ_bilinear
    exact h_double''
  have h₁ :
      freeCovarianceℂ_bilinear m (QFT.compTimeReflection fc) (QFT.compTimeReflection gc)
        = (freeCovarianceFormR m (QFT.compTimeReflectionReal f) (QFT.compTimeReflectionReal g) : ℂ) := by
    simpa [h_toComplex_comp f, h_toComplex_comp g, fc, gc]
      using (freeCovarianceℂ_bilinear_agrees_on_reals
        (m := m) (f := QFT.compTimeReflectionReal f) (g := QFT.compTimeReflectionReal g))
  have h₂ :
      freeCovarianceℂ_bilinear m fc gc
        = (freeCovarianceFormR m f g : ℂ) :=
    (freeCovarianceℂ_bilinear_agrees_on_reals (m := m) f g)
  have h_complex_eq :
      (freeCovarianceFormR m (QFT.compTimeReflectionReal f) (QFT.compTimeReflectionReal g) : ℂ)
        = (freeCovarianceFormR m f g : ℂ) := by
    calc
      (freeCovarianceFormR m (QFT.compTimeReflectionReal f) (QFT.compTimeReflectionReal g) : ℂ)
          = freeCovarianceℂ_bilinear m (QFT.compTimeReflection fc) (QFT.compTimeReflection gc) := h₁.symm
      _ = freeCovarianceℂ_bilinear m fc gc := h_complex
      _ = (freeCovarianceFormR m f g : ℂ) := h₂
  exact ofReal_inj.mp h_complex_eq

/-- Mixed-time-reflection identity for the real free covariance. -/
lemma freeCovarianceFormR_reflection_cross
    (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] (f g : SchwartzTestFunction d) :
    freeCovarianceFormR m (QFT.compTimeReflectionReal f) g
      = freeCovarianceFormR m (QFT.compTimeReflectionReal g) f := by
  classical
  have h_invol_f :
      QFT.compTimeReflectionReal (QFT.compTimeReflectionReal f) = f := by
    ext x
    change
        (QFT.compTimeReflectionReal
            (QFT.compTimeReflectionReal f) : SchwartzTestFunction d) x = f x
    have h_time :
        QFT.timeReflectionLinear (QFT.timeReflectionLinear x) = x :=
      QFT.timeReflection_involutive x
    simp [QFT.compTimeReflectionReal, QFT.timeReflectionCLM,
      QFT.timeReflectionLinear, QFT.timeReflection]
  have h_invol_g :
      QFT.compTimeReflectionReal (QFT.compTimeReflectionReal g) = g := by
    ext x
    change
        (QFT.compTimeReflectionReal
            (QFT.compTimeReflectionReal g) : SchwartzTestFunction d) x = g x
    have h_time :
        QFT.timeReflectionLinear (QFT.timeReflectionLinear x) = x :=
      QFT.timeReflection_involutive x
    simp [QFT.compTimeReflectionReal, QFT.timeReflectionCLM,
      QFT.timeReflectionLinear, QFT.timeReflection]
  have h_step :
      freeCovarianceFormR m (QFT.compTimeReflectionReal f) g
        = freeCovarianceFormR m f (QFT.compTimeReflectionReal g) := by
    simpa [h_invol_g]
      using freeCovarianceFormR_reflection_invariant (m := m)
        (f := f) (g := QFT.compTimeReflectionReal g)
  calc
    freeCovarianceFormR m (QFT.compTimeReflectionReal f) g
        = freeCovarianceFormR m f (QFT.compTimeReflectionReal g) := h_step
    _ = freeCovarianceFormR m (QFT.compTimeReflectionReal g) f := by
        exact freeCovarianceFormR_symm m f (compTimeReflectionReal g)

/-- Left linearity of freeCovarianceFormR for any fixed right argument. -/
lemma freeCovarianceFormR_left_linear_any_right
    (m : ℝ) [Fact (0 < m)] [GFFPropagator d m] {n : ℕ} (f : Fin n → PositiveTimeTestFunction d) (c : Fin n → ℝ)
    (s : Finset (Fin n)) (g : SchwartzTestFunction d) :
    ∑ i ∈ s, c i * freeCovarianceFormR m (QFT.compTimeReflectionReal (f i).val) g =
    freeCovarianceFormR m (∑ i ∈ s, c i • QFT.compTimeReflectionReal (f i).val) g := by
  induction' s using Finset.induction with k t hk ih
  · simp only [Finset.sum_empty]
    rw [← freeCovarianceFormR_zero_left (d := d) (m := m) g]
  · rw [Finset.sum_insert hk, Finset.sum_insert hk]
    have h_smul : c k * freeCovarianceFormR m (QFT.compTimeReflectionReal (f k).val) g =
      freeCovarianceFormR m (c k • QFT.compTimeReflectionReal (f k).val) g :=
      (freeCovarianceFormR_smul_left m (c k) (QFT.compTimeReflectionReal (f k).val) g).symm
    rw [h_smul, ih]
    rw [← freeCovarianceFormR_add_left]

end QFT

end
