import OSforGFF.FiniteDimGaussian
import OSforGFF.KolmogorovExtension
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

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

/-! ## Coordinate restriction between finite Euclidean spaces

For `J ⊆ I`, we will need the (continuous) linear map
`EuclideanSpace ℝ I → EuclideanSpace ℝ J` that restricts coordinates, and its adjoint (extension by
`0` outside `J`).  These maps are used to prove projectivity of the Gaussian family.
-/

section EuclideanRestrict

variable {I J : Finset ι} (hJI : J ⊆ I)

@[simp] private def incl (j : J) : I := ⟨j.1, hJI j.2⟩

/-- Coordinate restriction map `EuclideanSpace ℝ I → EuclideanSpace ℝ J` (as a linear map). -/
noncomputable def restrictEuclideanₗ : EuclideanSpace ℝ I →ₗ[ℝ] EuclideanSpace ℝ J where
  toFun x := toLp (2 : ℝ≥0∞) (fun j : J => (ofLp x) (incl (hJI := hJI) j))
  map_add' x y := by
    ext j
    simp [incl]
  map_smul' c x := by
    ext j
    simp [incl]

/-- Coordinate extension-by-zero map `EuclideanSpace ℝ J → EuclideanSpace ℝ I` (as a linear map). -/
noncomputable def extendEuclideanₗ : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ I where
  toFun x := by
    classical
    exact
      toLp (2 : ℝ≥0∞) (fun i : I => if hi : i.1 ∈ J then (ofLp x) ⟨i.1, hi⟩ else 0)
  map_add' x y := by
    classical
    ext i
    by_cases hi : i.1 ∈ J <;> simp [hi]
  map_smul' c x := by
    classical
    ext i
    by_cases hi : i.1 ∈ J <;> simp [hi]

/-- Coordinate restriction map as a continuous linear map. -/
noncomputable def restrictEuclidean : EuclideanSpace ℝ I →L[ℝ] EuclideanSpace ℝ J :=
  (restrictEuclideanₗ (hJI := hJI)).toContinuousLinearMap

/-- Coordinate extension-by-zero map as a continuous linear map. -/
noncomputable def extendEuclidean : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ I :=
  (extendEuclideanₗ (I := I) (J := J)).toContinuousLinearMap

@[simp]
lemma restrictEuclidean_apply (x : EuclideanSpace ℝ I) (j : J) :
    restrictEuclidean (I := I) (J := J) hJI x j = (ofLp x) (incl (hJI := hJI) j) := by
  simp [restrictEuclidean, restrictEuclideanₗ, incl]

@[simp]
lemma ofLp_restrictEuclidean (x : EuclideanSpace ℝ I) :
    ofLp (restrictEuclidean (I := I) (J := J) hJI x) =
      fun j : J => (ofLp x) (incl (hJI := hJI) j) := by
  rfl

@[simp]
lemma extendEuclidean_apply (x : EuclideanSpace ℝ J) (i : I) :
    extendEuclidean (I := I) (J := J) x i =
      (by
        classical
        exact if hi : i.1 ∈ J then (ofLp x) ⟨i.1, hi⟩ else 0) := by
  simp [extendEuclidean, extendEuclideanₗ]

lemma extendEuclidean_eq_adjoint_restrictEuclidean :
    extendEuclidean (I := I) (J := J) =
      (restrictEuclidean (I := I) (J := J) hJI).adjoint := by
  classical
  refine (ContinuousLinearMap.eq_adjoint_iff (A := extendEuclidean (I := I) (J := J))
    (B := restrictEuclidean (I := I) (J := J) hJI)).2 ?_
  intro x y
  simp [PiLp.inner_apply, RCLike.inner_apply, extendEuclidean_apply, restrictEuclidean_apply, incl]
  let s : Set I := { i : I | (i.1 : ι) ∈ J }
  have h₁ :
      (∑ i : I, (if hi : (i.1 : ι) ∈ J then y i * x ⟨i.1, hi⟩ else (0 : ℝ))) =
        ∑ i : s, y i.1 * x ⟨i.1.1, i.2⟩ := by
    classical
    refine Finset.sum_congr_set (ι := I) (s := s)
      (f := fun i : I => if hi : (i.1 : ι) ∈ J then y i * x ⟨i.1, hi⟩ else (0 : ℝ))
      (g := fun i : s => y i.1 * x ⟨i.1.1, i.2⟩) ?_ ?_
    · intro i hi
      have hiJ : (i.1 : ι) ∈ J := by simpa [s] using hi
      simp [hiJ]
    · intro i hi
      have hiJ : (i.1 : ι) ∉ J := by simpa [s] using hi
      simp [hiJ]
  let e : s ≃ J :=
    { toFun := fun i => ⟨i.1.1, i.2⟩
      invFun := fun j => ⟨incl (hJI := hJI) j, by simp [s]⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro j
        rfl }
  have h₂ :
      (∑ i : s, y i.1 * x ⟨i.1.1, i.2⟩) = ∑ j : J, y (incl (hJI := hJI) j) * x j := by
    classical
    refine Fintype.sum_equiv e
      (f := fun i : s => y i.1 * x ⟨i.1.1, i.2⟩)
      (g := fun j : J => y (incl (hJI := hJI) j) * x j) ?_
    intro i
    have hinc : incl (hJI := hJI) (e i) = i.1 := by
      apply Subtype.ext
      rfl
    simp [e]
  have hI : (I.attach : Finset I) = Finset.univ := by
    simp
  have hJ : (J.attach : Finset J) = Finset.univ := by
    simp
  rw [hI, hJ]
  simpa [incl] using h₁.trans h₂

@[simp] lemma restrictEuclidean_adjoint :
    (restrictEuclidean (I := I) (J := J) hJI).adjoint = extendEuclidean (I := I) (J := J) := by
  simp [extendEuclidean_eq_adjoint_restrictEuclidean (I := I) (J := J) hJI]

end EuclideanRestrict

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
