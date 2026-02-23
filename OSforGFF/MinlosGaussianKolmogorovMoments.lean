import OSforGFF.MinlosGaussianKolmogorov
import Mathlib.Probability.Moments.Variance

/-!
# Moments of the Gaussian Kolmogorov cylindrical measure

This file derives basic first/second-moment identities for the coordinate maps
`ω ↦ ω f` under the Kolmogorov-extension Gaussian process measure constructed in
`OSforGFF.MinlosGaussianKolmogorov`.
-/

open Complex MeasureTheory
open scoped RealInnerProductSpace ProbabilityTheory

namespace OSforGFF

noncomputable section

namespace MinlosGaussianKolmogorov

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The evaluation random variable has mean `0`. -/
theorem integral_eval_eq_zero (T : E →ₗ[ℝ] H) (f : E) :
    (∫ ω, (ω f : ℝ) ∂(gaussianProcess (E := E) (H := H) T)) = 0 := by
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  let evalF : (E → ℝ) → ℝ := fun ω => ω f
  have hmeas_evalF : Measurable evalF := by
    simpa [evalF] using (measurable_pi_apply f)
  have hmap : μ.map evalF = ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖T f‖ ^ 2)) := by
    simpa [μ, evalF] using (map_eval_eq_gaussianReal (E := E) (H := H) (T := T) f)
  have hAe : AEMeasurable evalF μ := hmeas_evalF.aemeasurable
  have hAS : AEStronglyMeasurable (fun x : ℝ => x) (μ.map evalF) :=
    (measurable_id : Measurable (fun x : ℝ => x)).aestronglyMeasurable
  have :
      (∫ x, x ∂(μ.map evalF)) = (∫ ω, evalF ω ∂μ) := by
    simpa using (MeasureTheory.integral_map (μ := μ) (φ := evalF) (f := fun x : ℝ => x)
      (hφ := hAe) (hfm := hAS))
  have hid : (∫ x, x ∂ProbabilityTheory.gaussianReal (0 : ℝ) (Real.toNNReal (‖T f‖ ^ 2))) = 0 := by
    simp [ProbabilityTheory.integral_id_gaussianReal]
  have :
      (∫ ω, evalF ω ∂μ) = 0 := by
    calc
      (∫ ω, evalF ω ∂μ) = (∫ x, x ∂(μ.map evalF)) := this.symm
      _ = (∫ x, x ∂ProbabilityTheory.gaussianReal (0 : ℝ) (Real.toNNReal (‖T f‖ ^ 2)) ) := by
            simp [hmap]
      _ = 0 := hid
  simpa [μ, evalF] using this

/-- The evaluation random variable has variance `‖T f‖²`. -/
theorem variance_eval_eq (T : E →ₗ[ℝ] H) (f : E) :
    Var[(fun ω : E → ℝ => ω f); gaussianProcess (E := E) (H := H) T] = (‖T f‖ ^ 2 : ℝ) := by
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  let evalF : (E → ℝ) → ℝ := fun ω => ω f
  have hmeas_evalF : AEMeasurable evalF μ := by
    simpa [evalF] using (measurable_pi_apply f).aemeasurable
  have hmap : μ.map evalF = ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖T f‖ ^ 2)) := by
    simpa [μ, evalF] using (map_eval_eq_gaussianReal (E := E) (H := H) (T := T) f)
  have hvar_id : Var[id; μ.map evalF] = Var[evalF; μ] := by
    simpa [μ, evalF] using (ProbabilityTheory.variance_id_map (μ := μ) (X := evalF) hmeas_evalF)
  have hvar_gauss : Var[id; μ.map evalF] = (Real.toNNReal (‖T f‖ ^ 2) : ℝ) := by
    simp [hmap, ProbabilityTheory.variance_id_gaussianReal]
  have hcoe : (Real.toNNReal (‖T f‖ ^ 2) : ℝ) = (‖T f‖ ^ 2 : ℝ) :=
    Real.coe_toNNReal _ (sq_nonneg ‖T f‖)
  have : Var[evalF; μ] = (‖T f‖ ^ 2 : ℝ) :=
    hvar_id.symm.trans (hvar_gauss.trans hcoe)
  simpa [μ, evalF] using this

/-- All moments of the evaluation random variable are finite. -/
theorem memLp_eval (T : E →ₗ[ℝ] H) (f : E) (p : ENNReal) (hp : p ≠ (⊤ : ENNReal)) :
    MemLp (fun ω : E → ℝ => ω f) p (gaussianProcess (E := E) (H := H) T) := by
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  let evalF : (E → ℝ) → ℝ := fun ω => ω f
  have hmeas_evalF : AEMeasurable evalF μ := by
    simpa [evalF] using (measurable_pi_apply f).aemeasurable
  have hmap : μ.map evalF = ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖T f‖ ^ 2)) := by
    simpa [μ, evalF] using (map_eval_eq_gaussianReal (E := E) (H := H) (T := T) f)
  have hMemLp_map : MemLp (fun x : ℝ => x) p (μ.map evalF) := by
    simpa [hmap] using
      (ProbabilityTheory.memLp_id_gaussianReal' (μ := (0 : ℝ))
        (v := Real.toNNReal (‖T f‖ ^ 2)) p hp)
  have hAS_id : AEStronglyMeasurable (fun x : ℝ => x) (μ.map evalF) :=
    (measurable_id : Measurable (fun x : ℝ => x)).aestronglyMeasurable
  have := (MeasureTheory.memLp_map_measure_iff (μ := μ) (f := evalF) (g := fun x : ℝ => x)
    (p := p) (hg := hAS_id) (hf := hmeas_evalF)).1 hMemLp_map
  simpa [μ, evalF] using this

end MinlosGaussianKolmogorov

end

end OSforGFF
