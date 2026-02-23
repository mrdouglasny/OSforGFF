/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.GaussianProcessKolmogorov
import OSforGFF.FiniteDimGaussianIsGaussian
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def

/-!
# `IsGaussian` for Kolmogorov finite-dimensional laws

This module provides `ProbabilityTheory.IsGaussian` instances for the finite-dimensional laws
`gaussianFiniteLaw` used in `OSforGFF.GaussianProcessKolmogorov`.

This is convenient for reusing mathlib's Gaussian API (extensionality by covariance/charfun, etc.)
when proving projectivity.
-/

open scoped BigOperators NNReal ENNReal InnerProductSpace RealInnerProductSpace MatrixOrder

open MeasureTheory Complex Matrix

namespace OSforGFF.GaussianProcessKolmogorov

noncomputable section

open ProbabilityTheory
open OSforGFF.FiniteDimGaussian
open WithLp (toLp ofLp)

variable {ι : Type*}

instance (K : ι → ι → ℝ) (J : Finset ι) (hJ : (covMatrix K J).PosSemidef) :
    ProbabilityTheory.IsGaussian (gaussianFiniteLaw (ι := ι) K J hJ) := by
  classical
  let e : EuclideanSpace ℝ J ≃L[ℝ] (J → ℝ) :=
    PiLp.continuousLinearEquiv (p := (2 : ℝ≥0∞)) (𝕜 := ℝ) (β := fun _ : J => ℝ)
  have : ProbabilityTheory.IsGaussian
      ((gaussianOfPosSemidef (n := J) (covMatrix K J) hJ).map e) := by
    infer_instance
  simpa [gaussianFiniteLaw, e, PiLp.coe_continuousLinearEquiv] using this

variable (K : ι → ι → ℝ) (hK : ∀ J : Finset ι, (covMatrix K J).PosSemidef)

/-- The finite-dimensional marginals of `gaussianProcessOfKernel` are Gaussian. -/
lemma hasGaussianLaw_restrict_gaussianProcessOfKernel (I : Finset ι) :
    ProbabilityTheory.HasGaussianLaw
      (fun ω : ι → ℝ => I.restrict ω)
      (gaussianProcessOfKernel (ι := ι) K hK) := by
  refine ⟨?_⟩
  have hmap : (gaussianProcessOfKernel (ι := ι) K hK).map (fun ω : ι → ℝ => I.restrict ω) =
      gaussianFiniteLaw (ι := ι) K I (hK I) := by
    simpa [gaussianFamily] using (isProjectiveLimit_gaussianProcessOfKernel (ι := ι) K hK I)
  simpa [hmap] using (by
    infer_instance : ProbabilityTheory.IsGaussian (gaussianFiniteLaw (ι := ι) K I (hK I)))

/-- Under `gaussianProcessOfKernel`, the coordinate evaluation process is a Gaussian process. -/
theorem isGaussianProcess_eval_gaussianProcessOfKernel :
    ProbabilityTheory.IsGaussianProcess (Ω := ι → ℝ) (E := ℝ) (T := ι)
      (fun i (ω : ι → ℝ) => ω i) (gaussianProcessOfKernel (ι := ι) K hK) := by
  refine ⟨fun I => ?_⟩
  simpa using (hasGaussianLaw_restrict_gaussianProcessOfKernel (ι := ι) (K := K) (hK := hK) I)

end

end OSforGFF.GaussianProcessKolmogorov
