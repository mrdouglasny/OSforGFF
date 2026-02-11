import OSforGFF.GaussianProcessKolmogorov
import OSforGFF.FiniteDimGaussianIsGaussian

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

end

end OSforGFF.GaussianProcessKolmogorov
