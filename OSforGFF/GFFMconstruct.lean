/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Gaussian.Basic
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

import OSforGFF.Basic
import OSforGFF.Schwinger
import OSforGFF.MinlosAxiomatic
import OSforGFF.Covariance
import OSforGFF.CovarianceR
import OSforGFF.MinlosAnalytic
import OSforGFF.ComplexTestFunction

/-!
## Gaussian Free Field Construction via Minlos Theorem

This file constructs Gaussian probability measures on field configurations using
the Minlos theorem. The key insight: a Gaussian measure is uniquely determined
by its covariance function, and nuclear covariances give measures on tempered distributions.

### Integrability strategy

To prove that Gaussian pairings belong to \(L^p\) under the free field measure, we use:

**Characteristic Function Bridge:** We prove `gff_pairing_is_gaussian` showing that the pushforward
of the GFF measure by any test function pairing is a 1D Gaussian measure. Since Gaussian measures
have finite moments of all orders (Mathlib's `memLp_id_gaussianReal`), this gives us the Lᵖ
integrability result `gaussianFreeField_pairing_memLp` as a theorem rather than an axiom.

This approach was implemented on 2025-12-16, replacing the previous axiomatic shortcut.

### Core Framework:

**Covariance Structure:**
- `CovarianceFunction`: Symmetric, bilinear, positive semidefinite covariance with boundedness
- `CovarianceNuclear`: Nuclear (trace class) condition required for Minlos theorem
- `SchwingerFunctionℂ₂`: Complex 2-point correlation function ⟨φ(f)φ(g)⟩

**Gaussian Characterization:**
- `isCenteredGJ`: Zero mean condition for Gaussian measures
- `isGaussianGJ`: Generating functional Z[J] = exp(-½⟨J, CJ⟩) for centered Gaussian

### Minlos Construction:

**Main Constructor:**
- `constructGaussianMeasureMinlos_free`: Specialized construction for free field via Minlos theorem

**Note:** A general Minlos construction for arbitrary nuclear covariance functions
was explored in `old/GeneralMinlos.lean` but is not used in the current formalization.

### Free Field Realization:

**Klein-Gordon Propagator:**
- `freeFieldPropagator`: C(k) = 1/(ik² + m²) in momentum space
- `freeFieldCovariance`: Covariance built from propagator via Fourier transform
- `freeFieldCovariance_nuclear`: Proof of nuclear condition for m > 0, d < 4

**Main Result:**
- `gaussianFreeField`: The Gaussian Free Field measure for mass m > 0

### Mathematical Foundation:

**Minlos Theorem:** For nuclear covariance C on Schwartz space S(ℝᵈ), there exists
unique probability measure μ on S'(ℝᵈ) with characteristic functional Z[f] = exp(-½⟨f,Cf⟩).

**Nuclear Condition:** Tr(C) = ∫ 1/(k² + m²) dk < ∞ for d < 4 (with m > 0).
Essential for extending cylindrical measures to σ-additive measures on S'(ℝᵈ).

**Advantages:** Direct infinite-dimensional construction without Kolmogorov extension,
standard approach in constructive QFT, handles dimension restrictions naturally.

### Integration:

**AQFT Connections:** Uses `Basic` (field configurations), `Minlos` (measure theory),
`Schwinger` (correlation functions), provides foundation for OS axiom verification.

Standard approach for constructing Gaussian Free Fields in quantum field theory.
-/

open MeasureTheory Complex QFT ProbabilityTheory
open TopologicalSpace SchwartzMap

/-! ## Axioms in this file

This file contains no axioms. All previously assumed axioms have been proved:
- `gaussianFreeField_free_centered`: proved via `moment_zero_from_realCF`
- `gaussianFreeField_pairing_memLp`: proved via `gff_pairing_is_gaussian` (characteristic function bridge)

Axioms used transitively (via imports): `schwartz_nuclear`, `minlos_theorem`, `minlos_uniqueness`.
-/

noncomputable section

/-! ## Gaussian Measures on Field Configurations
-/

/-- A covariance function on test functions that determines the Gaussian measure -/
structure CovarianceFunction where
  covar : TestFunctionℂ → TestFunctionℂ → ℂ
  symmetric : ∀ f g, covar f g = (starRingEnd ℂ) (covar g f)
  bilinear_left : ∀ c f₁ f₂ g, covar (c • f₁ + f₂) g = c * covar f₁ g + covar f₂ g
  bilinear_right : ∀ f c g₁ g₂, covar f (c • g₁ + g₂) = (starRingEnd ℂ) c * covar f g₁ + covar f g₂
  positive_semidefinite : ∀ f, 0 ≤ (covar f f).re
  bounded : ∃ M > 0, ∀ f, ‖covar f f‖ ≤ M * (∫ x, ‖f x‖ ∂volume) * (∫ x, ‖f x‖^2 ∂volume)^(1/2)

/-- A measure is centered (has zero mean) -/
def isCenteredGJ (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  ∀ (f : TestFunction), GJMean dμ_config f = 0

/-- A measure is Gaussian if its generating functional has the Gaussian form.
    For a centered Gaussian measure, Z[J] = exp(-½⟨J, CJ⟩) where C is the covariance. -/
def isGaussianGJ (dμ_config : ProbabilityMeasure FieldConfiguration) : Prop :=
  isCenteredGJ dμ_config ∧
  ∀ (J : TestFunctionℂ),
    GJGeneratingFunctionalℂ dμ_config J =
    Complex.exp (-(1/2 : ℂ) * SchwingerFunctionℂ₂ dμ_config J J)

/-! ## Construction via Minlos Theorem -/

/-- Nuclear space structure for real test functions.
    This is derived from the general `schwartz_nuclear` axiom in Minlos.lean
    applied to `TestFunction = SchwartzMap SpaceTime ℝ`. -/
instance instNuclear_TestFunction : NuclearSpace TestFunction := schwartz_nuclear

/-- Specialized Minlos construction for the free field using the square-root propagator embedding. -/
noncomputable def constructGaussianMeasureMinlos_free (m : ℝ) [Fact (0 < m)] :
  ProbabilityMeasure FieldConfiguration := by
  classical
  -- Build the embedding T with ‖T f‖² = freeCovarianceFormR m f f
  have ex1 := sqrtPropagatorEmbedding m
  let H : Type := Classical.choose ex1
  have ex2 := Classical.choose_spec ex1
  letI hNorm : NormedAddCommGroup H := Classical.choose ex2
  have ex3 := Classical.choose_spec ex2
  letI hInner : InnerProductSpace ℝ H := Classical.choose ex3
  have ex4 := Classical.choose_spec ex3
  let T : TestFunction →ₗ[ℝ] H := Classical.choose ex4
  have h_eq : ∀ f : TestFunction, freeCovarianceFormR m f f = ‖T f‖^2 := Classical.choose_spec ex4
  -- Continuity and normalization
  have h_cont := freeCovarianceFormR_continuous m
  have h_zero : freeCovarianceFormR m (0) (0) = 0 := by simp [freeCovarianceFormR]
  -- Use Minlos: directly obtain a ProbabilityMeasure with the Gaussian characteristic functional
  have h_minlos :=
    gaussian_measure_characteristic_functional
      (E := TestFunction) (H := H) T (freeCovarianceFormR m)
      (by intro f; simpa using h_eq f)
      h_zero h_cont
  exact Classical.choose h_minlos

/-- The Gaussian Free Field with mass m > 0, constructed via specialized Minlos -/
noncomputable def gaussianFreeField_free (m : ℝ) [Fact (0 < m)] : ProbabilityMeasure FieldConfiguration :=
  constructGaussianMeasureMinlos_free m

/-- Shorthand for the free GFF probability measure used throughout. -/
@[simp] abbrev μ_GFF (m : ℝ) [Fact (0 < m)] := gaussianFreeField_free m

/-- Real characteristic functional of the free GFF: for real test functions f, the generating
    functional equals the Gaussian form with the real covariance. -/
theorem gff_real_characteristic (m : ℝ) [Fact (0 < m)] :
  ∀ f : TestFunction,
    GJGeneratingFunctional (gaussianFreeField_free m) f =
      Complex.exp (-(1/2 : ℂ) * (freeCovarianceFormR m f f : ℝ)) := by
  classical
  -- Rebuild the same Minlos construction to access its specification
  have ex1 := sqrtPropagatorEmbedding m
  let H : Type := Classical.choose ex1
  have ex2 := Classical.choose_spec ex1
  letI hNorm : NormedAddCommGroup H := Classical.choose ex2
  have ex3 := Classical.choose_spec ex2
  letI hInner : InnerProductSpace ℝ H := Classical.choose ex3
  have ex4 := Classical.choose_spec ex3
  let T : TestFunction →ₗ[ℝ] H := Classical.choose ex4
  have h_eq : ∀ f : TestFunction, freeCovarianceFormR m f f = ‖T f‖^2 := Classical.choose_spec ex4
  have h_cont := freeCovarianceFormR_continuous m
  have h_zero : freeCovarianceFormR m (0) (0) = 0 := by simp [freeCovarianceFormR]
  have h_minlos :=
    gaussian_measure_characteristic_functional
      (E := TestFunction) (H := H) T (freeCovarianceFormR m)
      (by intro f; simpa using h_eq f)
      h_zero h_cont
  -- Unfold the definition of our chosen ProbabilityMeasure to reuse the spec
  have hchar := (Classical.choose_spec h_minlos)
  intro f
  -- By definition, gaussianFreeField_free chooses the same ProbabilityMeasure
  -- returned by gaussian_measure_characteristic_functional
  simpa [gaussianFreeField_free, constructGaussianMeasureMinlos_free,
        GJGeneratingFunctional, gaussian_characteristic_functional,
        distributionPairing]
    using (hchar f)

/-! ### Characteristic Function Bridge

These lemmas connect the GFF characteristic functional to 1D Gaussian pushforwards,
proving that the axiom `gaussianFreeField_pairing_memLp` can be derived from first principles.
-/

/-- If a probability measure has the characteristic function of a Gaussian,
    then it is that Gaussian measure (Lévy uniqueness). -/
private lemma charFun_implies_gaussian
  (μ : Measure ℝ) [IsProbabilityMeasure μ]
  (mean : ℝ) (σ : NNReal)
  (h : ∀ t : ℝ, charFun μ t = Complex.exp (I * (t * mean) - (1/2 : ℂ) * (σ : ℝ) * t^2)) :
  μ = gaussianReal mean σ := by
  apply Measure.ext_of_charFun
  funext t
  rw [h t, charFun_gaussianReal]
  ring_nf

/-- The characteristic function of a pushforward measure by `distributionPairingCLM φ`
    equals the generating functional at a scaled test function. -/
private lemma charFun_eq_GJGeneratingFunctional
  (μ : ProbabilityMeasure FieldConfiguration) (φ : TestFunction) (t : ℝ)
  [IsProbabilityMeasure (μ.toMeasure.map (distributionPairingCLM φ))] :
  charFun (μ.toMeasure.map (distributionPairingCLM φ)) t =
    GJGeneratingFunctional μ (t • φ) := by
  rw [charFun]
  rw [integral_map (by fun_prop) (by fun_prop)]
  rw [GJGeneratingFunctional]
  congr 1
  ext ω
  congr 1
  simp only [distributionPairingCLM, ContinuousLinearMap.coe_mk', real_inner_comm]
  rw [mul_comm _ I]
  congr 1
  simp [distributionPairing]
  ring

/-- For the GFF measure, the pushforward by `distributionPairingCLM φ` has
    the characteristic function of a centered Gaussian with variance `freeCovarianceFormR m φ φ`. -/
private lemma gff_pushforward_charFun
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) (t : ℝ) :
  charFun ((gaussianFreeField_free m).toMeasure.map (distributionPairingCLM φ)) t =
    Complex.exp (-(1/2 : ℂ) * t^2 * (freeCovarianceFormR m φ φ : ℝ)) := by
  haveI : IsProbabilityMeasure ((gaussianFreeField_free m).toMeasure.map (distributionPairingCLM φ)) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (distributionPairingCLM φ).continuous.measurable)
  rw [charFun_eq_GJGeneratingFunctional]
  have h_char := gff_real_characteristic m (t • φ)
  rw [h_char]
  congr 1
  rw [freeCovarianceFormR_smul_left, freeCovarianceFormR_smul_right]
  push_cast
  ring

/-- The pushforward of the GFF measure by pairing with a test function is a 1D Gaussian.
    Proven via characteristic functions and Lévy's uniqueness theorem. -/
theorem gff_pairing_is_gaussian
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  (gaussianFreeField_free m).toMeasure.map (distributionPairingCLM φ)
    = gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal := by
  haveI : IsProbabilityMeasure ((gaussianFreeField_free m).toMeasure.map (distributionPairingCLM φ)) :=
    Measure.isProbabilityMeasure_map (Measurable.aemeasurable (distributionPairingCLM φ).continuous.measurable)
  apply charFun_implies_gaussian
  intro t
  rw [gff_pushforward_charFun]
  simp only [mul_zero, Complex.ofReal_zero]
  congr 1
  have h_pos : 0 ≤ freeCovarianceFormR m φ φ := freeCovarianceFormR_pos m φ
  rw [Real.coe_toNNReal _ h_pos]
  ring

/-- **Fernique's Theorem for GFF**: Every distribution pairing has finite moments of all orders.

    This is proven using characteristic functions:
    1. `gff_pairing_is_gaussian` shows the pushforward is a 1D Gaussian
    2. Gaussian measures on ℝ have finite moments (Mathlib's `memLp_id_gaussianReal`)
    3. Pull back through the measurable pairing map

    This theorem was formerly an axiom, now proven via the characteristic function bridge. -/
theorem gaussianFreeField_pairing_memLp
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) (p : ENNReal) (hp : p ≠ ⊤) :
  MemLp (distributionPairingCLM φ) p (gaussianFreeField_free m).toMeasure := by
  -- The pushforward measure is a 1D Gaussian
  have h_gauss := gff_pairing_is_gaussian m φ
  -- Convert to use the fact that id is memLp for the Gaussian
  have hp_coe : p = ENNReal.ofNNReal p.toNNReal := (ENNReal.coe_toNNReal hp).symm
  rw [hp_coe]
  have h_memLp : MemLp id (ENNReal.ofNNReal p.toNNReal) (gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal) :=
    memLp_id_gaussianReal p.toNNReal
  rw [← h_gauss] at h_memLp
  rwa [memLp_map_measure_iff (by fun_prop) (by fun_prop)] at h_memLp

/-- The GFF pairing has an integrable square (is in L²).
    This follows from the fact that the pushforward is a Gaussian measure,
    and Gaussian measures have finite moments of all orders. -/
lemma gff_pairing_square_integrable
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  Integrable (fun ω => (distributionPairingCLM φ ω)^2) (gaussianFreeField_free m).toMeasure := by
  -- The pushforward measure is Gaussian
  have h_gauss := gff_pairing_is_gaussian m φ
  -- For a Gaussian measure, id is in L²
  have h_memL2 : MemLp id 2 (gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal) :=
    memLp_id_gaussianReal 2
  -- Rewrite in terms of the pushforward measure
  rw [← h_gauss] at h_memL2
  -- MemLp id under the pushforward equals MemLp of the original function
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)] at h_memL2
  -- For real-valued functions, MemLp 2 means square-integrable
  exact h_memL2.integrable_sq

/-- The second moment of the GFF pairing equals the covariance form.
    This follows from the fact that the pushforward is a Gaussian with variance
    equal to the covariance form, and for centered Gaussians, variance = second moment. -/
lemma gff_second_moment_eq_covariance
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  ∫ ω, (distributionPairingCLM φ ω)^2 ∂(gaussianFreeField_free m).toMeasure =
    freeCovarianceFormR m φ φ := by
  -- The pushforward is a Gaussian measure
  have h_gauss := gff_pairing_is_gaussian m φ
  -- Rewrite the integral as an integral under the pushforward measure
  calc ∫ ω, (distributionPairingCLM φ ω)^2 ∂(gaussianFreeField_free m).toMeasure
    _ = ∫ x, x^2 ∂((gaussianFreeField_free m).toMeasure.map (distributionPairingCLM φ)) := by
      rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ x, x^2 ∂(gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal) := by
      rw [h_gauss]
    _ = (freeCovarianceFormR m φ φ).toNNReal := by
      -- For centered Gaussian, variance equals second moment
      have h_var_eq : Var[fun x => x; gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal] =
          ∫ x, x^2 ∂(gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal) := by
        have h_mean : (gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal)[fun x => x] = 0 := by
          simp [integral_id_gaussianReal]
        exact variance_of_integral_eq_zero (by fun_prop) h_mean
      rw [← h_var_eq]
      exact variance_fun_id_gaussianReal
    _ = freeCovarianceFormR m φ φ := by
      simp [Real.coe_toNNReal', freeCovarianceFormR_pos]

/-- The Gaussian CF with the free covariance is positive definite,
    via the square-root propagator embedding into a Hilbert space. -/
lemma freeCovarianceFormR_gaussian_cf_pd (m : ℝ) [Fact (0 < m)] :
    IsPositiveDefinite
      (fun f : TestFunction => Complex.exp (-(1/2 : ℂ) * (freeCovarianceFormR m f f : ℂ))) := by
  have ex1 := sqrtPropagatorEmbedding m
  let H : Type := Classical.choose ex1
  have ex2 := Classical.choose_spec ex1
  letI hNorm : NormedAddCommGroup H := Classical.choose ex2
  have ex3 := Classical.choose_spec ex2
  letI hInner : InnerProductSpace ℝ H := Classical.choose ex3
  have ex4 := Classical.choose_spec ex3
  let T : TestFunction →ₗ[ℝ] H := Classical.choose ex4
  have h_eq : ∀ f : TestFunction, freeCovarianceFormR m f f = ‖T f‖^2 := Classical.choose_spec ex4
  exact gaussian_positive_definite_via_embedding T (freeCovarianceFormR m) h_eq

/-- The free covariance form as a MinlosAnalytic.CovarianceForm structure. -/
def freeCovarianceForm (m : ℝ) [Fact (0 < m)] : MinlosAnalytic.CovarianceForm :=
  { Q := freeCovarianceFormR m
    symm := freeCovarianceFormR_symm m
    psd := freeCovarianceFormR_pos m
    cont_diag := freeCovarianceFormR_continuous m
    add_left := freeCovarianceFormR_add_left m
    smul_left := freeCovarianceFormR_smul_left m
    gaussian_cf_pd := freeCovarianceFormR_gaussian_cf_pd m }

/-- The GFF has zero mean: the measure is centered.

    Proof: The characteristic functional `gff_real_characteristic` shows that
    Z[f] = exp(-½⟨f,Cf⟩) depends only on the quadratic form freeCovarianceFormR m f f,
    which is symmetric under f ↦ -f. By `integral_neg_invariance`, the measure is
    invariant under ω ↦ -ω. From this negation invariance:
      GJMean μ φ = ∫ ⟨ω,φ⟩ dμ = ∫ ⟨-ω,φ⟩ dμ = -∫ ⟨ω,φ⟩ dμ
    implying GJMean μ φ = 0. -/
theorem gaussianFreeField_free_centered (m : ℝ) [Fact (0 < m)] :
    isCenteredGJ (gaussianFreeField_free m) := by
  intro φ
  unfold GJMean
  -- Step 1: Get the real CF hypothesis from gff_real_characteristic
  have h_realCF : ∀ f : TestFunction,
      ∫ ω, Complex.exp (Complex.I * (ω f)) ∂(gaussianFreeField_free m).toMeasure
        = Complex.exp (-(1/2 : ℂ) * ((freeCovarianceForm m).Q f f)) := by
    intro f
    have h := gff_real_characteristic m f
    simp only [GJGeneratingFunctional, distributionPairing] at h
    exact h
  -- Step 2: Get integrability from gaussianFreeField_pairing_memLp
  have hInt : Integrable (fun ω => (ω φ : ℂ)) (gaussianFreeField_free m).toMeasure := by
    have h_memLp := gaussianFreeField_pairing_memLp m φ 1 (by norm_num : (1 : ENNReal) ≠ ⊤)
    -- MemLp f 1 μ implies Integrable f μ
    have h_int_real : Integrable (distributionPairingCLM φ) (gaussianFreeField_free m).toMeasure :=
      h_memLp.integrable (by norm_num : (1 : ENNReal) ≤ 1)
    -- The complex version follows since ofReal is continuous
    exact h_int_real.ofReal
  -- Step 3: Apply moment_zero_from_realCF to get ∫ (ω φ : ℂ) = 0
  have h_complex_zero : ∫ ω, (ω φ : ℂ) ∂(gaussianFreeField_free m).toMeasure = 0 :=
    MinlosAnalytic.moment_zero_from_realCF (freeCovarianceForm m) (gaussianFreeField_free m) h_realCF φ hInt
  -- Step 4: Convert from complex to real integral
  -- The integral ∫ (ω φ : ℂ) = ofReal(∫ ω φ) by integral_ofReal
  -- So if ∫ (ω φ : ℂ) = 0, then ∫ ω φ = 0
  have h_ofReal : ∫ ω, (ω φ : ℂ) ∂(gaussianFreeField_free m).toMeasure =
                  Complex.ofReal (∫ ω, ω φ ∂(gaussianFreeField_free m).toMeasure) := by
    exact integral_ofReal
  rw [h_ofReal] at h_complex_zero
  exact Complex.ofReal_eq_zero.mp h_complex_zero

/-- **Fernique's Theorem for GFF (exponential form)**: For every real test function `φ`,
there exists `α > 0` such that `exp(α * ⟨ω, φ⟩²)` is integrable under the free GFF measure.

This follows from `gff_pairing_is_gaussian` which shows the pushforward is a 1D Gaussian,
combined with Mathlib's `IsGaussian.exists_integrable_exp_sq` (Fernique's theorem).

Proven 2025-12-16, replacing the previous axiom. -/
theorem gaussianFreeField_pairing_expSq_integrable
  (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  ∃ α : ℝ, 0 < α ∧
    Integrable
      (fun ω =>
        Real.exp (α * (distributionPairingCLM φ ω)^2))
      (gaussianFreeField_free m).toMeasure := by
  -- The pushforward is a 1D Gaussian
  have h_gauss := gff_pairing_is_gaussian m φ
  -- Apply Fernique's theorem to the Gaussian measure
  obtain ⟨C, hC_pos, hC_int⟩ := IsGaussian.exists_integrable_exp_sq
    (gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal)
  -- C > 0 works
  refine ⟨C, hC_pos, ?_⟩
  -- Rewrite using h_gauss: the Gaussian equals the pushforward
  rw [← h_gauss] at hC_int
  -- Pull back through the measurable pairing map
  rw [integrable_map_measure (by fun_prop) (by fun_prop)] at hC_int
  -- Convert ‖x‖² to x² for ℝ (they are equal for real numbers)
  convert hC_int using 2
  -- Goal: exp (C * y²) = exp (C * ‖y‖²) where y : ℝ
  simp only [Function.comp_apply]
  congr 1
  rw [Real.norm_eq_abs, sq_abs]

/-- For real test functions, the square of the Gaussian pairing is integrable under the
    free Gaussian Free Field measure. This is the diagonal (f = g) case needed for
    establishing two-point integrability. -/
lemma gaussian_pairing_square_integrable_real
    (m : ℝ) [Fact (0 < m)] (φ : TestFunction) :
  Integrable (fun ω => (distributionPairing ω φ) ^ 2)
    (gaussianFreeField_free m).toMeasure := by
  -- Option B: invoke the Fernique-type axiom giving Lᵖ moments for the pairing
  have h_memLp :=
    gaussianFreeField_pairing_memLp m φ ((2 : ℕ) : ENNReal) (by simp)
  -- L² membership directly implies integrability of the square
  have h_integrable_CLM := h_memLp.integrable_sq
  -- Translate the statement from the continuous linear map to the scalar pairing
  simpa [distributionPairingCLM_apply] using h_integrable_CLM

end
