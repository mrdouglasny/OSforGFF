import OSforGFF.Minlos
import OSforGFF.MinlosGaussianToWeakDual
import OSforGFF.MinlosGaussianSupportNuclearL2

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Gaussian Minlos (proved core, conditional on support)

We connect the Gaussian Kolmogorov construction to the `gaussian_characteristic_functional`
API from `OSforGFF.Minlos`.

At this stage we still assume the (hard) support/measurable-embedding hypotheses needed to descend
the Kolmogorov measure on `E → ℝ` to `WeakDual ℝ E`. Once those hypotheses are proved from
nuclearity, this will yield an axiom-free replacement for the Gaussian uses of `minlos_theorem`.
-/

open scoped BigOperators
open scoped RealInnerProductSpace

open MeasureTheory Complex

namespace OSforGFF

noncomputable section

namespace MinlosGaussianProved

open OSforGFF.MinlosGaussianToWeakDual
open OSforGFF.MinlosGaussianSupport

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Work with the Borel σ-algebra on `WeakDual`.
instance : MeasurableSpace (WeakDual ℝ E) := borel _

/-- **Gaussian measure on `WeakDual` (conditional version).**

Assuming the Kolmogorov Gaussian process measure `gaussianProcess T` is concentrated on the image
of the coercion `WeakDual ℝ E → (E → ℝ)`, construct the corresponding probability measure on
`WeakDual` and compute its characteristic functional.
-/
theorem gaussian_measure_characteristic_functional_of_ae_range
    (T : E →ₗ[ℝ] H)
    (h_embed : MeasurableEmbedding (toFun (E := E)))
    (h_ae_range :
      ∀ᵐ ω ∂(MinlosGaussianKolmogorov.gaussianProcess (E := E) (H := H) T),
        ω ∈ Set.range (toFun (E := E))) :
    ∃ μ : MeasureTheory.ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E,
        (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂μ.toMeasure)
          =
            gaussian_characteristic_functional
              (MinlosGaussianKolmogorov.kernel (E := E) (H := H) T) f := by
  classical
  refine ⟨gaussianProcessWeakDual (E := E) (H := H) T h_embed h_ae_range, ?_⟩
  intro f
  -- we use the Kolmogorov identity transported to `WeakDual`, then rewrite the RHS.
  have h :=
    MinlosGaussianToWeakDual.integral_exp_eval_eq (E := E) (H := H) (T := T)
      (h_embed := h_embed) (h_ae_range := h_ae_range) f
  simpa [gaussian_characteristic_functional, MinlosGaussianKolmogorov.kernel,
    inner_self_eq_norm_sq] using h

/-- Same as `gaussian_measure_characteristic_functional_of_ae_range`, but stated in terms of an
arbitrary covariance form that agrees with `‖T f‖²` on the diagonal (the only input used by
`gaussian_characteristic_functional`). -/
theorem gaussian_measure_characteristic_functional_of_ae_range'
    (T : E →ₗ[ℝ] H)
    (covariance_form : E → E → ℝ)
    (h_eq : ∀ f, covariance_form f f = (‖T f‖ ^ 2 : ℝ))
    (h_embed : MeasurableEmbedding (toFun (E := E)))
    (h_ae_range :
      ∀ᵐ ω ∂(MinlosGaussianKolmogorov.gaussianProcess (E := E) (H := H) T),
        ω ∈ Set.range (toFun (E := E))) :
    ∃ μ : MeasureTheory.ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E,
        (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂μ.toMeasure)
          = gaussian_characteristic_functional covariance_form f := by
  classical
  obtain ⟨μ, hμ⟩ :=
    gaussian_measure_characteristic_functional_of_ae_range (E := E) (H := H) T h_embed h_ae_range
  refine ⟨μ, ?_⟩
  intro f
  have :
      gaussian_characteristic_functional
          (MinlosGaussianKolmogorov.kernel (E := E) (H := H) T) f
        = gaussian_characteristic_functional covariance_form f := by
    simp [gaussian_characteristic_functional, MinlosGaussianKolmogorov.kernel, h_eq]
  simpa [this] using hμ f

/-!
## A canonical descended Gaussian measure (conditional on measurable embedding)

For downstream use it is convenient to package the support theorem into an actual definition of the
Gaussian probability measure on `WeakDual ℝ E`.
-/

theorem exists_gaussianProcessWeakDual_of_nuclear
    [OSforGFF.NuclearSpaceStd E]
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ μ : MeasureTheory.ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E,
        (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂μ.toMeasure) =
          Complex.exp (-(1 / 2 : ℂ) * (‖T f‖ ^ 2 : ℝ)) := by
  classical
  -- Choose seminorm bound + nuclear inclusion.
  rcases MinlosGaussianSupport.exists_seminormFamily_bound (E := E) (H := H) T h_sq with
    ⟨n, C, _hC0, hle⟩
  rcases MinlosGaussianSupport.exists_nuclear_inclusion (E := E) (n := n) with ⟨m, hnm, hNuc⟩
  -- Push forward the Kolmogorov Gaussian measure along the measurable `WeakDual`-valued modification.
  let μProd : Measure (E → ℝ) := MinlosGaussianKolmogorov.gaussianProcess (E := E) (H := H) T
  let ν : MeasureTheory.ProbabilityMeasure (E → ℝ) := ⟨μProd, by infer_instance⟩
  let ωWD : (E → ℝ) → WeakDual ℝ E :=
    MinlosGaussianSupport.omegaModWeakDual
      (E := E) (H := H) (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc)
  have hωWD_meas : Measurable ωWD := by
    simpa [ωWD] using
      (MinlosGaussianSupport.measurable_omegaModWeakDual
        (E := E) (H := H) (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc))
  let μ : MeasureTheory.ProbabilityMeasure (WeakDual ℝ E) :=
    ν.map hωWD_meas.aemeasurable
  refine ⟨μ, ?_⟩
  intro f
  -- Change variables along the pushforward, then use a.e. modification to reduce to Kolmogorov.
  have h_integrand_meas :
      Measurable (fun ω : WeakDual ℝ E => Complex.exp (I * ((ω f : ℝ) : ℂ))) := by
    fun_prop
  have h_map :
      (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂(Measure.map ωWD μProd)) =
        ∫ ω, Complex.exp (I * (((ωWD ω) f : ℝ) : ℂ)) ∂μProd := by
    -- `integral_map` for the measurable map `ωWD`.
    have h :=
      (MeasureTheory.integral_map (μ := μProd) (φ := ωWD)
        (hωWD_meas.aemeasurable)
        (f := fun ω : WeakDual ℝ E => Complex.exp (I * ((ω f : ℝ) : ℂ)))
        (h_integrand_meas.aestronglyMeasurable))
    simpa using h
  -- Rewrite the LHS as the integral under `μ`.
  have hμ_toMeasure :
      μ.toMeasure = Measure.map ωWD μProd := by
    rfl
  -- Now compare with the Kolmogorov integral.
  have hAE_eval :
      (fun ω : E → ℝ => (ωWD ω) f) =ᵐ[μProd] fun ω : E → ℝ => ω f := by
    -- This is exactly `omegaModWeakDual_eval_ae_eq`.
    simpa [ωWD, μProd] using
      (MinlosGaussianSupport.omegaModWeakDual_eval_ae_eq
        (E := E) (H := H) (T := T) (hle := hle) (hnm := hnm) (m := m) (hNuc := hNuc) f)
  have hAE_exp :
      (fun ω : E → ℝ => Complex.exp (I * (((ωWD ω) f : ℝ) : ℂ)))
        =ᵐ[μProd]
          fun ω : E → ℝ => Complex.exp (I * ((ω f : ℝ) : ℂ)) := by
    filter_upwards [hAE_eval] with ω hω
    simp [hω]
  calc
    (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂μ.toMeasure)
        = ∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂(Measure.map ωWD μProd) := by
            simp [hμ_toMeasure]
    _ = ∫ ω, Complex.exp (I * (((ωWD ω) f : ℝ) : ℂ)) ∂μProd := h_map
    _ = ∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂μProd := by
            exact integral_congr_ae hAE_exp
    _ = Complex.exp (-(1 / 2 : ℂ) * (‖T f‖ ^ 2 : ℝ)) := by
          simpa [μProd] using
            (OSforGFF.MinlosGaussianKolmogorov.integral_exp_eval_eq (E := E) (H := H) (T := T) f)

/-- The Gaussian probability measure on `WeakDual ℝ E` obtained by descending the Kolmogorov
Gaussian process measure along `toFun`, using the nuclear `L²` support theorem. -/
noncomputable def gaussianProcessWeakDual_of_nuclear
    [OSforGFF.NuclearSpaceStd E]
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    MeasureTheory.ProbabilityMeasure (WeakDual ℝ E) :=
  Classical.choose (exists_gaussianProcessWeakDual_of_nuclear (E := E) (H := H) (T := T) h_sq)

/-- Characteristic-functional identity for `gaussianProcessWeakDual_of_nuclear`. -/
theorem integral_exp_eval_eq_gaussianProcessWeakDual_of_nuclear
    [OSforGFF.NuclearSpaceStd E]
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ))
    (f : E) :
    (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ))
        ∂(gaussianProcessWeakDual_of_nuclear (E := E) (H := H) (T := T) h_sq).toMeasure) =
      Complex.exp (-(1 / 2 : ℂ) * (‖T f‖ ^ 2 : ℝ)) := by
  simpa [gaussianProcessWeakDual_of_nuclear] using
    (Classical.choose_spec
      (exists_gaussianProcessWeakDual_of_nuclear (E := E) (H := H) (T := T) h_sq) f)

/-- **Gaussian Minlos (proved, conditional on measurable embedding).**

Assuming `E` is a `NuclearSpaceStd` and `‖T ·‖²` is continuous, the support theorem gives the
almost-sure range hypothesis needed to descend `gaussianProcess T` to `WeakDual ℝ E`.

This removes the need to *assume* the a.s.-range hypothesis in downstream applications. -/
theorem gaussian_measure_characteristic_functional
    [OSforGFF.NuclearSpaceStd E]
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ μ : MeasureTheory.ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E,
        (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂μ.toMeasure)
          =
            gaussian_characteristic_functional
              (MinlosGaussianKolmogorov.kernel (E := E) (H := H) T) f := by
  classical
  refine ⟨gaussianProcessWeakDual_of_nuclear (E := E) (H := H) (T := T) h_sq, ?_⟩
  intro f
  have h :=
    integral_exp_eval_eq_gaussianProcessWeakDual_of_nuclear
      (E := E) (H := H) (T := T) (h_sq := h_sq) f
  simpa [gaussian_characteristic_functional, MinlosGaussianKolmogorov.kernel,
    inner_self_eq_norm_sq] using h

/-- Variant of `gaussian_measure_characteristic_functional` with an arbitrary diagonal covariance
form, using a witness `T` such that `covariance_form f f = ‖T f‖²`. -/
theorem gaussian_measure_characteristic_functional'
    [OSforGFF.NuclearSpaceStd E]
    (T : E →ₗ[ℝ] H)
    (covariance_form : E → E → ℝ)
    (h_eq : ∀ f, covariance_form f f = (‖T f‖ ^ 2 : ℝ))
    (h_cont : Continuous fun f => covariance_form f f)
    :
    ∃ μ : MeasureTheory.ProbabilityMeasure (WeakDual ℝ E),
      ∀ f : E,
        (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂μ.toMeasure)
          = gaussian_characteristic_functional covariance_form f := by
  classical
  -- Reduce to the `‖T ·‖²` statement, then rewrite the RHS using `h_eq`.
  have h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ) := by
    simpa [h_eq] using h_cont
  obtain ⟨μ, hμ⟩ :=
    gaussian_measure_characteristic_functional (E := E) (H := H) (T := T) h_sq
  refine ⟨μ, ?_⟩
  intro f
  -- Rewrite the kernel-diagonal characteristic functional as the target diagonal form.
  have :
      gaussian_characteristic_functional (MinlosGaussianKolmogorov.kernel (E := E) (H := H) T) f
        = gaussian_characteristic_functional covariance_form f := by
    simp [gaussian_characteristic_functional, MinlosGaussianKolmogorov.kernel, h_eq]
  simpa [this] using hμ f

end MinlosGaussianProved

end

end OSforGFF
