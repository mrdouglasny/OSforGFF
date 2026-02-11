import OSforGFF.FiniteDimGaussian
import OSforGFF.KolmogorovExtension
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Gaussian processes via Kolmogorov extension (finite-dimensional Gaussians)

This file provides the **Kolmogorov-extension** part of the (Gaussian) Minlos strategy:

* from a covariance kernel `K : ι → ι → ℝ`, build for each `J : Finset ι` a finite-dimensional
  centered Gaussian law on `∀ j : J, ℝ` with covariance matrix `K` restricted to `J`;
* prove the resulting family is **projective**;
* obtain the projective-limit measure `μ : Measure (ι → ℝ)` using `KolmogorovExtension4`.

At this stage we only construct the measure on the **canonical product measurable space**
(`MeasurableSpace.pi`) on `ι → ℝ`.  Descending to a measure on a smaller path space (e.g. the weak
dual of a nuclear space) is a separate, strictly harder step.
-/

open scoped BigOperators NNReal ENNReal InnerProductSpace RealInnerProductSpace MatrixOrder

open MeasureTheory Complex Matrix

namespace OSforGFF

noncomputable section

namespace GaussianProcessKolmogorov

open OSforGFF.FiniteDimGaussian
open WithLp (toLp ofLp)

variable {ι : Type*}

/-! ## Covariance matrices on finite sets -/

/-- Restrict a kernel `K : ι → ι → ℝ` to a covariance matrix on a finite set `J`. -/
def covMatrix (K : ι → ι → ℝ) (J : Finset ι) : Matrix J J ℝ :=
  fun i j => K i.1 j.1

/-! ## Finite-dimensional laws -/

/-- The centered Gaussian law on `J → ℝ` with covariance matrix `covMatrix K J`.

We build the law on `EuclideanSpace ℝ J` and transport it to the underlying Π-type via `ofLp`. -/
def gaussianFiniteLaw (K : ι → ι → ℝ) (J : Finset ι)
    (hJ : (covMatrix K J).PosSemidef) : Measure (J → ℝ) := by
  classical
  exact (gaussianOfPosSemidef (n := J) (covMatrix K J) hJ).map ofLp

instance (K : ι → ι → ℝ) (J : Finset ι) (hJ : (covMatrix K J).PosSemidef) :
    IsProbabilityMeasure (gaussianFiniteLaw (ι := ι) K J hJ) := by
  classical
  simpa [gaussianFiniteLaw] using
    (Measure.isProbabilityMeasure_map
      (μ := gaussianOfPosSemidef (n := J) (covMatrix K J) hJ)
      (f := (ofLp : EuclideanSpace ℝ J → J → ℝ))
      ((WithLp.measurable_ofLp (p := (2 : ℝ≥0∞)) (X := J → ℝ)).aemeasurable))

/-! ## The projective Gaussian family -/

/-- The Gaussian finite-dimensional distribution family associated to `K`, given a proof that all
finite restrictions are positive semidefinite. -/
def gaussianFamily (K : ι → ι → ℝ)
    (hK : ∀ J : Finset ι, (covMatrix K J).PosSemidef) :
    ∀ J : Finset ι, Measure (J → ℝ) :=
  fun J => gaussianFiniteLaw (ι := ι) K J (hK J)

instance (K : ι → ι → ℝ)
    (hK : ∀ J : Finset ι, (covMatrix K J).PosSemidef) (J : Finset ι) :
    IsProbabilityMeasure (gaussianFamily (ι := ι) K hK J) := by
  classical
  dsimp [gaussianFamily]
  infer_instance

/-! ## The Kolmogorov extension measure -/

/-- The (centered) Gaussian process measure on the full product space `ι → ℝ`,
obtained as the Kolmogorov projective limit of a *projective* finite-dimensional family.

This definition is parameterized by a proof of projectivity; proving that the Gaussian family
associated to a given kernel is projective is a separate lemma. -/
noncomputable def gaussianProcess (K : ι → ι → ℝ)
    (hK : ∀ J : Finset ι, (covMatrix K J).PosSemidef)
    (hproj :
      MeasureTheory.IsProjectiveMeasureFamily (ι := ι) (α := fun _ : ι => ℝ)
        (gaussianFamily (ι := ι) K hK)) :
    Measure (ι → ℝ) :=
  MeasureTheory.projectiveLimit (ι := ι) (α := fun _ : ι => ℝ) (gaussianFamily (ι := ι) K hK) hproj

end GaussianProcessKolmogorov

end

end OSforGFF
