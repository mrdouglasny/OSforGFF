import OSforGFF.Minlos
import OSforGFF.MinlosGaussianToWeakDual

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Gaussian Minlos (proved core, conditional on support)

This file connects the Gaussian Kolmogorov construction to the `gaussian_characteristic_functional`
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
  -- Use the Kolmogorov identity transported to `WeakDual`, then rewrite the RHS.
  have h :=
    MinlosGaussianToWeakDual.integral_exp_eval_eq (E := E) (H := H) (T := T)
      (h_embed := h_embed) (h_ae_range := h_ae_range) f
  -- `kernel T f f = ‖T f‖^2`, so the exponential matches `gaussian_characteristic_functional`.
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
  -- Rewrite the RHS using `h_eq` and the diagonal of `kernel`.
  have :
      gaussian_characteristic_functional
          (MinlosGaussianKolmogorov.kernel (E := E) (H := H) T) f
        = gaussian_characteristic_functional covariance_form f := by
    simp [gaussian_characteristic_functional, MinlosGaussianKolmogorov.kernel, h_eq]
  simpa [this] using hμ f

end MinlosGaussianProved

end

end OSforGFF

