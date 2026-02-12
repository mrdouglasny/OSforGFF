import OSforGFF.MinlosGaussianKolmogorov
import OSforGFF.WeakDualMeasurability

import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Gaussian Kolmogorov measure → `WeakDual` (conditional descent)

This file formalizes the **measure-theoretic descent** step of the Gaussian Minlos pipeline:

* we start from the Kolmogorov-extension Gaussian measure `gaussianProcess T` on the product space
  `E → ℝ`;
* assuming (later, to be proved) that this measure is concentrated on the image of the coercion
  `WeakDual ℝ E → (E → ℝ)`, we can pull it back to a probability measure on `WeakDual ℝ E`;
* the characteristic-functional identity then follows from the corresponding identity on
  `E → ℝ` (proved in `OSforGFF.MinlosGaussianKolmogorov`).

The genuinely hard work is proving the concentration assumption; this file makes that assumption
explicit and derives the clean downstream consequences.
-/

open scoped BigOperators

open MeasureTheory Complex

namespace OSforGFF

noncomputable section

namespace MinlosGaussianToWeakDual

open OSforGFF.MinlosGaussianKolmogorov

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- We work with the Borel σ-algebra on `WeakDual`.
instance : MeasurableSpace (WeakDual ℝ E) := borel _

/-- The coercion `WeakDual ℝ E → (E → ℝ)` (forgetting linearity/continuity structure). -/
def toFun : WeakDual ℝ E → (E → ℝ) := fun ω => fun f => ω f

lemma toFun_apply (ω : WeakDual ℝ E) (f : E) : toFun (E := E) ω f = ω f := rfl

lemma toFun_injective : Function.Injective (toFun (E := E)) := by
  intro ω₁ ω₂ h
  apply DFunLike.ext
  intro f
  simpa [toFun] using congrArg (fun g : E → ℝ => g f) h

/-!
## The pulled-back measure on `WeakDual`
-/

/-- Assuming `gaussianProcess T` is a.s. in the range of `toFun`, pull it back to `WeakDual`. -/
def gaussianProcessWeakDual
    (T : E →ₗ[ℝ] H)
    (h_embed : MeasurableEmbedding (toFun (E := E)))
    (h_ae_range : ∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T), ω ∈ Set.range (toFun (E := E))) :
    MeasureTheory.ProbabilityMeasure (WeakDual ℝ E) :=
  ⟨(gaussianProcess (E := E) (H := H) T).comap (toFun (E := E)),
    (MeasurableEmbedding.isProbabilityMeasure_comap (μ := gaussianProcess (E := E) (H := H) T)
      h_embed h_ae_range)⟩

@[simp]
lemma gaussianProcessWeakDual_toMeasure
    (T : E →ₗ[ℝ] H)
    (h_embed : MeasurableEmbedding (toFun (E := E)))
    (h_ae_range : ∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T), ω ∈ Set.range (toFun (E := E))) :
    (gaussianProcessWeakDual (E := E) (H := H) T h_embed h_ae_range).toMeasure =
      (gaussianProcess (E := E) (H := H) T).comap (toFun (E := E)) :=
  rfl

/-!
## Characteristic functional identity
-/

theorem integral_exp_eval_eq
    (T : E →ₗ[ℝ] H)
    (h_embed : MeasurableEmbedding (toFun (E := E)))
    (h_ae_range : ∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T), ω ∈ Set.range (toFun (E := E)))
    (f : E) :
    (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ))
        ∂(gaussianProcessWeakDual (E := E) (H := H) T h_embed h_ae_range).toMeasure) =
      Complex.exp (-(1 / 2 : ℂ) * (‖T f‖ ^ 2 : ℝ)) := by
  let μProd : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  let μWD : MeasureTheory.ProbabilityMeasure (WeakDual ℝ E) :=
    gaussianProcessWeakDual (E := E) (H := H) T h_embed h_ae_range
  have h_map :
      (μWD.toMeasure.map (toFun (E := E))) = μProd := by
    have h0 :
        ((μProd.comap (toFun (E := E))).map (toFun (E := E)))
          = μProd.restrict (Set.range (toFun (E := E))) := by
      simpa [μProd] using (h_embed.map_comap μProd)
    have h_restrict : μProd.restrict (Set.range (toFun (E := E))) = μProd :=
      Measure.restrict_eq_self_of_ae_mem h_ae_range
    simpa [μWD, μProd, gaussianProcessWeakDual_toMeasure (E := E) (H := H) (T := T)
      (h_embed := h_embed) (h_ae_range := h_ae_range)] using h0.trans h_restrict
  let g : (E → ℝ) → ℂ := fun ω => Complex.exp (I * ((ω f : ℝ) : ℂ))
  have h_int :
      (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂μWD.toMeasure)
        = ∫ ω, g ω ∂(μWD.toMeasure.map (toFun (E := E))) := by
    symm
    simpa [g, toFun] using (h_embed.integral_map (μ := μWD.toMeasure) (g := g))
  calc
    (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂μWD.toMeasure)
        = ∫ ω, g ω ∂(μWD.toMeasure.map (toFun (E := E))) := h_int
    _ = ∫ ω, g ω ∂μProd := by simp [h_map]
    _ = Complex.exp (-(1 / 2 : ℂ) * (‖T f‖ ^ 2 : ℝ)) := by
          simpa [μProd, g] using
            (OSforGFF.MinlosGaussianKolmogorov.integral_exp_eval_eq (E := E) (H := H) (T := T) f)

end MinlosGaussianToWeakDual

end
end OSforGFF
