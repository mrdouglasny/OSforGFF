import OSforGFF.Basic
import OSforGFF.CovarianceR
import OSforGFF.Minlos.GelfandTriple
import OSforGFF.MinlosGaussianProved

import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Free GFF via Kolmogorov + nuclear support

This file provides a **non-axiomatic** Gaussian measure construction on
`FieldConfiguration = WeakDual ℝ TestFunction` using the Kolmogorov Gaussian process and the
`NuclearSpaceStd` support theorem (`OSforGFF.MinlosGaussianSupportNuclearL2`).

Compared to `OSforGFF/GFFMconstruct.lean`, this does **not** use the axioms
`minlos_theorem`/`minlos_uniqueness`.

The only remaining hypothesis here is the (deep) **Schwartz nuclearity** input needed by the
support theorem.  Concretely, we assume `[OSforGFF.NuclearSpaceStd TestFunction]`; the module
`OSforGFF/NuclearSpace/Schwartz.lean` provides a canonical seminorm sequence for `TestFunction`
and packages the remaining gap as `OSforGFF.SchwartzNuclearInclusion`, which implies the needed
`NuclearSpaceStd TestFunction` instance.

In the spacetime Hermite model, this gap is discharged; see
`OSforGFF.NuclearSpace.PhysHermiteSpaceTimeSchwartzNuclearInclusion`.
-/

open MeasureTheory Complex ProbabilityTheory
open scoped BigOperators RealInnerProductSpace

noncomputable section

namespace QFT

open OSforGFF

namespace GFFMconstructProved

open OSforGFF.MinlosGaussianToWeakDual
open OSforGFF.MinlosGaussianProved

/-- Continuity of the squared norm `f ↦ ‖embeddingMap m f‖²`. -/
lemma continuous_norm_embeddingMap_sq (m : ℝ) [Fact (0 < m)] :
    Continuous fun f : TestFunction => (‖embeddingMap m f‖ ^ 2 : ℝ) := by
  have hT : Continuous (embeddingMap m) := embeddingMap_continuous (m := m)
  have hnorm : Continuous fun f : TestFunction => ‖embeddingMap m f‖ := Continuous.norm hT
  simpa using (Continuous.pow hnorm 2)

/-- The free Gaussian Free Field measure, constructed via the Kolmogorov Gaussian process together
with the nuclear `L²` support theorem.

This construction is conditional on:
`[OSforGFF.NuclearSpaceStd TestFunction]`. -/
noncomputable def gaussianFreeField_free_proved (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    ProbabilityMeasure FieldConfiguration :=
  gaussianProcessWeakDual_of_nuclear
    (E := TestFunction) (H := TargetHilbertSpace m) (T := embeddingMap m)
    (h_sq := continuous_norm_embeddingMap_sq (m := m))

/-!
## The GFF as a Gel'fand triple

We package the proved GFF construction into the abstract `Minlos.GelfandTriple` API:

- `N = TestFunction`,
- `H = TargetHilbertSpace m`,
- `N' = WeakDual ℝ N`,
- `toHilbert = embeddingMapCLM m` (a continuous version of `embeddingMap m`).

This is the key “universality boundary”: downstream measure-theoretic code can depend only on the
abstract triple interface, not on the Fourier/Hermite implementation used to prove nuclearity.
-/

/-- The concrete Gel'fand triple underlying the free GFF measure construction. -/
noncomputable def gffGelfandTriple (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    OSforGFF.Minlos.GelfandTriple where
  N := TestFunction
  H := TargetHilbertSpace m
  toHilbert := embeddingMapCLM (m := m)

@[simp] lemma gffGelfandTriple_toHilbert_apply (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] (f : TestFunction) :
    (gffGelfandTriple (m := m)).toHilbert f = embeddingMap m f := by
  simpa [gffGelfandTriple] using (embeddingMapCLM_apply (m := m) f)

/-- The proved free GFF measure, expressed through the abstract Gel'fand triple API. -/
noncomputable def gaussianFreeField_free_proved_ofTriple (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    ProbabilityMeasure FieldConfiguration :=
  OSforGFF.Minlos.gaussianMeasureOfTriple (T := gffGelfandTriple (m := m))

theorem gaussianFreeField_free_proved_eq_ofTriple (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    gaussianFreeField_free_proved (m := m) = gaussianFreeField_free_proved_ofTriple (m := m) := by
  simp [gaussianFreeField_free_proved, gaussianFreeField_free_proved_ofTriple,
    OSforGFF.Minlos.gaussianMeasureOfTriple, gffGelfandTriple]
  have hT :
      ((embeddingMapCLM (m := m) : TestFunction →L[ℝ] TargetHilbertSpace m) :
          TestFunction →ₗ[ℝ] TargetHilbertSpace m) =
        embeddingMap m := by
    apply LinearMap.ext
    intro f
    exact embeddingMapCLM_apply (m := m) f
  simp [hT]


/-- Real characteristic functional of `gaussianFreeField_free_proved`: for real test functions `f`,
the generating functional has the Gaussian form with covariance `freeCovarianceFormR`. -/
theorem gff_real_characteristic_proved (m : ℝ) [Fact (0 < m)]
    [OSforGFF.NuclearSpaceStd TestFunction] :
    ∀ f : TestFunction,
      GJGeneratingFunctional (gaussianFreeField_free_proved (m := m)) f =
        Complex.exp (-(1 / 2 : ℂ) * (freeCovarianceFormR m f f : ℝ)) := by
  intro f
  have h_sq :
      Continuous fun f : TestFunction => (‖embeddingMap m f‖ ^ 2 : ℝ) :=
    continuous_norm_embeddingMap_sq (m := m)
  have h :=
    integral_exp_eval_eq_gaussianProcessWeakDual_of_nuclear
      (E := TestFunction) (H := TargetHilbertSpace m) (T := embeddingMap m)
      (h_sq := h_sq) f
  have h_eq : (‖embeddingMap m f‖ ^ 2 : ℝ) = freeCovarianceFormR m f f := by
    simpa using (freeCovarianceFormR_eq_normSq (m := m) (f := f)).symm
  simpa [gaussianFreeField_free_proved, GJGeneratingFunctional, distributionPairing, h_eq] using h

/-!
## Characteristic function bridge (proved construction)

As in `OSforGFF/GFFMconstruct.lean`, we can identify 1D pushforwards of the field by test-function
pairings as Gaussian measures on `ℝ`, and hence obtain `Lᵖ` integrability for all `p < ⊤`.
-/

/-- If a probability measure has the characteristic function of a Gaussian, then it is that
Gaussian measure (Lévy uniqueness). -/
private lemma charFun_implies_gaussian
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (mean : ℝ) (σ : NNReal)
    (h : ∀ t : ℝ, charFun μ t =
      Complex.exp (I * (t * mean) - (1 / 2 : ℂ) * (σ : ℝ) * t ^ 2)) :
    μ = gaussianReal mean σ := by
  apply Measure.ext_of_charFun
  funext t
  rw [h t, charFun_gaussianReal]
  ring_nf

/-- The characteristic function of a pushforward by `distributionPairingCLM φ` is the generating
functional evaluated at a scaled test function. -/
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

/-- For `gaussianFreeField_free_proved`, the pushforward by pairing with `φ` has the characteristic
function of a centered Gaussian with variance `freeCovarianceFormR m φ φ`. -/
private lemma gff_pushforward_charFun_proved
    (m : ℝ) [Fact (0 < m)] [OSforGFF.NuclearSpaceStd TestFunction]
    (φ : TestFunction) (t : ℝ) :
    charFun ((gaussianFreeField_free_proved (m := m)).toMeasure.map (distributionPairingCLM φ)) t =
      Complex.exp (-(1 / 2 : ℂ) * t ^ 2 * (freeCovarianceFormR m φ φ : ℝ)) := by
  haveI :
      IsProbabilityMeasure
        ((gaussianFreeField_free_proved (m := m)).toMeasure.map (distributionPairingCLM φ)) :=
    Measure.isProbabilityMeasure_map
      (Measurable.aemeasurable (distributionPairingCLM φ).continuous.measurable)
  rw [charFun_eq_GJGeneratingFunctional]
  have h_char := gff_real_characteristic_proved (m := m) (t • φ)
  rw [h_char]
  congr 1
  rw [freeCovarianceFormR_smul_left, freeCovarianceFormR_smul_right]
  push_cast
  ring

/-- The pushforward of `gaussianFreeField_free_proved` by pairing with a test function is a 1D
Gaussian measure. -/
theorem gff_pairing_is_gaussian_proved
    (m : ℝ) [Fact (0 < m)] [OSforGFF.NuclearSpaceStd TestFunction]
    (φ : TestFunction) :
    (gaussianFreeField_free_proved (m := m)).toMeasure.map (distributionPairingCLM φ)
      = gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal := by
  haveI :
      IsProbabilityMeasure
        ((gaussianFreeField_free_proved (m := m)).toMeasure.map (distributionPairingCLM φ)) :=
    Measure.isProbabilityMeasure_map
      (Measurable.aemeasurable (distributionPairingCLM φ).continuous.measurable)
  apply charFun_implies_gaussian
  intro t
  rw [gff_pushforward_charFun_proved (m := m) (φ := φ)]
  simp only [mul_zero, Complex.ofReal_zero]
  congr 1
  have h_pos : 0 ≤ freeCovarianceFormR m φ φ := freeCovarianceFormR_pos m φ
  rw [Real.coe_toNNReal _ h_pos]
  ring

/-- Fernique-style `Lᵖ` integrability of the pairing under `gaussianFreeField_free_proved`, proved
by identifying the pushforward measure as Gaussian. -/
theorem gaussianFreeField_pairing_memLp_proved
    (m : ℝ) [Fact (0 < m)] [OSforGFF.NuclearSpaceStd TestFunction]
    (φ : TestFunction) (p : ENNReal) (hp : p ≠ ⊤) :
    MemLp (distributionPairingCLM φ) p (gaussianFreeField_free_proved (m := m)).toMeasure := by
  have h_gauss := gff_pairing_is_gaussian_proved (m := m) φ
  have hp_coe : p = ENNReal.ofNNReal p.toNNReal := (ENNReal.coe_toNNReal hp).symm
  rw [hp_coe]
  have h_memLp :
      MemLp id (ENNReal.ofNNReal p.toNNReal)
        (gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal) :=
    memLp_id_gaussianReal p.toNNReal
  rw [← h_gauss] at h_memLp
  rwa [memLp_map_measure_iff (by fun_prop) (by fun_prop)] at h_memLp

/-- The pairing has an integrable square (i.e. lies in `L²`) under `gaussianFreeField_free_proved`. -/
lemma gff_pairing_square_integrable_proved
    (m : ℝ) [Fact (0 < m)] [OSforGFF.NuclearSpaceStd TestFunction]
    (φ : TestFunction) :
    Integrable (fun ω => (distributionPairingCLM φ ω) ^ 2)
      (gaussianFreeField_free_proved (m := m)).toMeasure := by
  have h_gauss := gff_pairing_is_gaussian_proved (m := m) φ
  have h_memL2 :
      MemLp id 2 (gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal) :=
    memLp_id_gaussianReal 2
  rw [← h_gauss] at h_memL2
  rw [memLp_map_measure_iff (by fun_prop) (by fun_prop)] at h_memL2
  simpa [pow_two] using h_memL2.integrable_sq

/-- The second moment of the pairing equals the covariance form. -/
lemma gff_second_moment_eq_covariance_proved
    (m : ℝ) [Fact (0 < m)] [OSforGFF.NuclearSpaceStd TestFunction]
    (φ : TestFunction) :
    ∫ ω, (distributionPairingCLM φ ω) ^ 2 ∂(gaussianFreeField_free_proved (m := m)).toMeasure =
      freeCovarianceFormR m φ φ := by
  have h_gauss := gff_pairing_is_gaussian_proved (m := m) φ
  calc
    ∫ ω, (distributionPairingCLM φ ω) ^ 2 ∂(gaussianFreeField_free_proved (m := m)).toMeasure
        = ∫ x, x ^ 2 ∂((gaussianFreeField_free_proved (m := m)).toMeasure.map (distributionPairingCLM φ)) := by
          rw [integral_map (by fun_prop) (by fun_prop)]
    _ = ∫ x, x ^ 2 ∂(gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal) := by
          rw [h_gauss]
    _ = (freeCovarianceFormR m φ φ).toNNReal := by
          have h_var_eq :
              Var[fun x => x; gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal] =
                ∫ x, x ^ 2 ∂(gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal) := by
            have h_mean :
                (gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal)[fun x => x] = 0 := by
              simp [integral_id_gaussianReal]
            exact variance_of_integral_eq_zero (by fun_prop) h_mean
          rw [← h_var_eq]
          exact variance_fun_id_gaussianReal
    _ = freeCovarianceFormR m φ φ := by
          simp [Real.coe_toNNReal', freeCovarianceFormR_pos]

/-- The mean pairing is zero (centeredness in each test-function direction). -/
lemma gff_mean_eq_zero_proved
    (m : ℝ) [Fact (0 < m)] [OSforGFF.NuclearSpaceStd TestFunction]
    (φ : TestFunction) :
    GJMean (gaussianFreeField_free_proved (m := m)) φ = 0 := by
  have h_gauss := gff_pairing_is_gaussian_proved (m := m) φ
  unfold GJMean
  have h_map :
      (∫ ω, distributionPairing ω φ
          ∂(gaussianFreeField_free_proved (m := m)).toMeasure) =
        ∫ x, x ∂((gaussianFreeField_free_proved (m := m)).toMeasure.map
          (distributionPairingCLM φ)) := by
    have h :=
      (MeasureTheory.integral_map
        (μ := (gaussianFreeField_free_proved (m := m)).toMeasure)
        (φ := distributionPairingCLM φ)
        ((distributionPairingCLM φ).continuous.measurable.aemeasurable)
        (f := fun x : ℝ => x)
        (measurable_id.aestronglyMeasurable))
    simpa [distributionPairingCLM_apply, distributionPairing] using h.symm
  calc
    (∫ ω, distributionPairing ω φ
        ∂(gaussianFreeField_free_proved (m := m)).toMeasure)
        = ∫ x, x ∂((gaussianFreeField_free_proved (m := m)).toMeasure.map
            (distributionPairingCLM φ)) := h_map
    _ = ∫ x, x ∂(gaussianReal 0 (freeCovarianceFormR m φ φ).toNNReal) := by
          simpa using congrArg (fun ν : Measure ℝ => (∫ x, x ∂ν)) h_gauss
    _ = 0 := by
          simp [integral_id_gaussianReal]

end GFFMconstructProved

end QFT
