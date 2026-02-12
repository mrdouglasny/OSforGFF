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
  map_add' x y := by ext j; simp [incl]
  map_smul' c x := by ext j; simp [incl]

/-- Coordinate extension-by-zero map `EuclideanSpace ℝ J → EuclideanSpace ℝ I` (as a linear map). -/
noncomputable def extendEuclideanₗ : EuclideanSpace ℝ J →ₗ[ℝ] EuclideanSpace ℝ I where
  toFun x := by
    classical
    exact toLp (2 : ℝ≥0∞) (fun i : I => if hi : i.1 ∈ J then (ofLp x) ⟨i.1, hi⟩ else 0)
  map_add' x y := by
    classical
    ext i; by_cases hi : i.1 ∈ J <;> simp [hi]
  map_smul' c x := by
    classical
    ext i; by_cases hi : i.1 ∈ J <;> simp [hi]

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

/-! ### Projectivity of the Gaussian family -/

section Projective

variable (K : ι → ι → ℝ)
variable (hK : ∀ J : Finset ι, (covMatrix K J).PosSemidef)

open scoped Classical InnerProduct

-- The key finite-dimensional consistency lemma on `EuclideanSpace`.
lemma restrict_toEuclideanCLM_extend {I J : Finset ι} (hJI : J ⊆ I) (x : EuclideanSpace ℝ J) :
    restrictEuclidean (I := I) (J := J) hJI
        ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) (covMatrix K I))
          (extendEuclidean (I := I) (J := J) x)) =
      (Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) (covMatrix K J)) x := by
  classical
  ext j
  simp only [restrictEuclidean_apply, Matrix.ofLp_toEuclideanCLM, extendEuclidean_apply, Matrix.mulVec,
    dotProduct]
  let s : Set I := { i : I | (i.1 : ι) ∈ J }
  have h₁ :
      (∑ i : I,
          covMatrix K I ⟨j.1, hJI j.2⟩ i *
            (if hi : (i.1 : ι) ∈ J then x ⟨i.1, hi⟩ else (0 : ℝ))) =
        ∑ i : s, covMatrix K I ⟨j.1, hJI j.2⟩ i.1 * x ⟨i.1.1, i.2⟩ := by
    classical
    refine Finset.sum_congr_set (ι := I) (s := s)
      (f := fun i : I =>
        covMatrix K I ⟨j.1, hJI j.2⟩ i *
          (if hi : (i.1 : ι) ∈ J then x ⟨i.1, hi⟩ else (0 : ℝ)))
      (g := fun i : s => covMatrix K I ⟨j.1, hJI j.2⟩ i.1 * x ⟨i.1.1, i.2⟩) ?_ ?_
    · intro i hi
      have hiJ : (i.1 : ι) ∈ J := by simpa [s] using hi
      simp [hiJ]
    · intro i hi
      have hiJ : (i.1 : ι) ∉ J := by simpa [s] using hi
      simp [hiJ]
  let e : s ≃ J :=
    { toFun := fun i => ⟨i.1.1, i.2⟩
      invFun := fun j' => ⟨⟨j'.1, hJI j'.2⟩, by simp [s] ⟩
      left_inv := by
        intro i
        apply Subtype.ext
        apply Subtype.ext
        rfl
      right_inv := by
        intro j'
        rfl }
  have h₂ :
      (∑ i : s, covMatrix K I ⟨j.1, hJI j.2⟩ i.1 * x ⟨i.1.1, i.2⟩) =
        ∑ j' : J, covMatrix K I ⟨j.1, hJI j.2⟩ ⟨j'.1, hJI j'.2⟩ * x j' := by
    classical
    refine Fintype.sum_equiv e
      (f := fun i : s => covMatrix K I ⟨j.1, hJI j.2⟩ i.1 * x ⟨i.1.1, i.2⟩)
      (g := fun j' : J => covMatrix K I ⟨j.1, hJI j.2⟩ ⟨j'.1, hJI j'.2⟩ * x j') ?_
    intro i
    simp [e]
  calc
    (∑ i : I,
        covMatrix K I ⟨j.1, hJI j.2⟩ i *
          (if hi : (i.1 : ι) ∈ J then x ⟨i.1, hi⟩ else (0 : ℝ))) =
        ∑ i : s, covMatrix K I ⟨j.1, hJI j.2⟩ i.1 * x ⟨i.1.1, i.2⟩ := h₁
    _ = ∑ j' : J, covMatrix K I ⟨j.1, hJI j.2⟩ ⟨j'.1, hJI j'.2⟩ * x j' := h₂
    _ = ∑ j' : J, covMatrix K J j j' * x j' := by
          simp [covMatrix]

-- Mapping the `I`-Gaussian by coordinate restriction gives the `J`-Gaussian.
lemma gaussianOfPosSemidef_map_restrictEuclidean {I J : Finset ι} (hJI : J ⊆ I) :
    (gaussianOfPosSemidef (n := I) (covMatrix K I) (hK I)).map
        (restrictEuclidean (I := I) (J := J) hJI) =
      gaussianOfPosSemidef (n := J) (covMatrix K J) (hK J) := by
  classical
  refine MeasureTheory.Measure.ext_of_charFun (μ :=
      (gaussianOfPosSemidef (n := I) (covMatrix K I) (hK I)).map
        (restrictEuclidean (I := I) (J := J) hJI))
    (ν := gaussianOfPosSemidef (n := J) (covMatrix K J) (hK J)) ?_
  funext t
  have hmap :=
    charFun_map_continuousLinearMap
      (μ := gaussianOfPosSemidef (n := I) (covMatrix K I) (hK I))
      (L := restrictEuclidean (I := I) (J := J) hJI) (t := t)
  have hadj :
      (restrictEuclidean (I := I) (J := J) hJI).adjoint t =
        extendEuclidean (I := I) (J := J) t := by
    simp
  have hinner :
      ⟪extendEuclidean (I := I) (J := J) t,
          (Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) (covMatrix K I))
            (extendEuclidean (I := I) (J := J) t)⟫_ℝ =
        ⟪t, (Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) (covMatrix K J)) t⟫_ℝ := by
    have hR :
        ⟪(restrictEuclidean (I := I) (J := J) hJI).adjoint t,
            (Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) (covMatrix K I))
              (extendEuclidean (I := I) (J := J) t)⟫_ℝ =
          ⟪t,
              restrictEuclidean (I := I) (J := J) hJI
                ((Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) (covMatrix K I))
                  (extendEuclidean (I := I) (J := J) t))⟫_ℝ := by
      simpa using
        (ContinuousLinearMap.adjoint_inner_left
          (A := restrictEuclidean (I := I) (J := J) hJI)
          (x := (Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) (covMatrix K I))
                (extendEuclidean (I := I) (J := J) t))
          (y := t))
    simpa [hadj, restrict_toEuclideanCLM_extend (K := K) (I := I) (J := J) hJI] using hR
  have hIchar :
      MeasureTheory.charFun
          ((gaussianOfPosSemidef (n := I) (covMatrix K I) (hK I)).map
            (restrictEuclidean (I := I) (J := J) hJI)) t =
        Complex.exp (-(1 / 2 : ℂ) *
          ⟪extendEuclidean (I := I) (J := J) t,
            (Matrix.toEuclideanCLM (n := I) (𝕜 := ℝ) (covMatrix K I))
              (extendEuclidean (I := I) (J := J) t)⟫_ℝ) := by
    simpa [hmap, hadj] using
      (charFun_gaussianOfPosSemidef (n := I) (covMatrix K I) (hK I)
        (t := extendEuclidean (I := I) (J := J) t))
  have hJchar :
      MeasureTheory.charFun (gaussianOfPosSemidef (n := J) (covMatrix K J) (hK J)) t =
        Complex.exp (-(1 / 2 : ℂ) *
          ⟪t, (Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) (covMatrix K J)) t⟫_ℝ) := by
    simpa using (charFun_gaussianOfPosSemidef (n := J) (covMatrix K J) (hK J) (t := t))
  simpa [hIchar, hJchar, hinner]

-- Projectivity for the transported measures on the plain Π-type `J → ℝ`.
lemma gaussianFamily_isProjective :
    MeasureTheory.IsProjectiveMeasureFamily (ι := ι) (α := fun _ : ι => ℝ)
      (gaussianFamily (ι := ι) K hK) := by
  intro I J hJI
  classical
  dsimp [gaussianFamily, gaussianFiniteLaw]
  set μI : Measure (EuclideanSpace ℝ I) :=
    gaussianOfPosSemidef (n := I) (covMatrix K I) (hK I)
  set μJ : Measure (EuclideanSpace ℝ J) :=
    gaussianOfPosSemidef (n := J) (covMatrix K J) (hK J)
  have hmeas_ofLpI : Measurable (ofLp : EuclideanSpace ℝ I → I → ℝ) := by fun_prop
  have hmeas_ofLpJ : Measurable (ofLp : EuclideanSpace ℝ J → J → ℝ) := by fun_prop
  have hmeas_restrict₂ :
      Measurable (Finset.restrict₂ (π := fun _ : ι => ℝ) hJI) := by
    simpa using (Finset.measurable_restrict₂ (X := fun _ : ι => ℝ) hJI)
  have hmeas_restrictEuclidean :
      Measurable (restrictEuclidean (I := I) (J := J) hJI) := by
    exact (restrictEuclidean (I := I) (J := J) hJI).continuous.measurable
  have hcomp :
      (Finset.restrict₂ (π := fun _ : ι => ℝ) hJI) ∘ (ofLp : EuclideanSpace ℝ I → I → ℝ) =
        (ofLp : EuclideanSpace ℝ J → J → ℝ) ∘
          (restrictEuclidean (I := I) (J := J) hJI) := by
    funext y
    ext j
    simp [Finset.restrict₂_def]
  calc
    Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) μJ
        = Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ)
            (Measure.map (restrictEuclidean (I := I) (J := J) hJI) μI) := by
            simpa [μI, μJ] using
              congrArg (fun ν => Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) ν)
                (gaussianOfPosSemidef_map_restrictEuclidean (K := K) (hK := hK) (I := I) (J := J)
                  hJI).symm
    _ = Measure.map ((ofLp : EuclideanSpace ℝ J → J → ℝ) ∘
            (restrictEuclidean (I := I) (J := J) hJI)) μI := by
          simpa [Measure.map_map hmeas_ofLpJ hmeas_restrictEuclidean, μI]
    _ = Measure.map ((Finset.restrict₂ (π := fun _ : ι => ℝ) hJI) ∘
            (ofLp : EuclideanSpace ℝ I → I → ℝ)) μI := by
          simpa [hcomp]
    _ = (Measure.map (Finset.restrict₂ (π := fun _ : ι => ℝ) hJI)
            (Measure.map (ofLp : EuclideanSpace ℝ I → I → ℝ) μI)) := by
          symm
          simpa [Measure.map_map hmeas_restrict₂ hmeas_ofLpI, μI]

end Projective

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

/-- The Gaussian process measure associated to `K`, obtained by proving projectivity of the
finite-dimensional family `gaussianFamily K hK`. -/
noncomputable def gaussianProcessOfKernel (K : ι → ι → ℝ)
    (hK : ∀ J : Finset ι, (covMatrix K J).PosSemidef) : Measure (ι → ℝ) :=
  gaussianProcess (ι := ι) K hK (gaussianFamily_isProjective (ι := ι) K hK)

theorem isProjectiveLimit_gaussianProcessOfKernel (K : ι → ι → ℝ)
    (hK : ∀ J : Finset ι, (covMatrix K J).PosSemidef) :
    MeasureTheory.IsProjectiveLimit (ι := ι) (α := fun _ : ι => ℝ)
      (gaussianProcessOfKernel (ι := ι) K hK) (gaussianFamily (ι := ι) K hK) := by
  classical
  simpa [gaussianProcessOfKernel, gaussianProcess] using
    (MeasureTheory.isProjectiveLimit_projectiveLimit
      (ι := ι) (α := fun _ : ι => ℝ) (P := gaussianFamily (ι := ι) K hK)
      (gaussianFamily_isProjective (ι := ι) K hK))

instance (K : ι → ι → ℝ) (hK : ∀ J : Finset ι, (covMatrix K J).PosSemidef) [Nonempty ι] :
    IsProbabilityMeasure (gaussianProcessOfKernel (ι := ι) K hK) := by
  classical
  simpa [gaussianProcessOfKernel, gaussianProcess] using
    (MeasureTheory.isProbabilityMeasure_projectiveLimit (ι := ι) (α := fun _ : ι => ℝ)
      (P := gaussianFamily (ι := ι) K hK)
      (gaussianFamily_isProjective (ι := ι) K hK))

end GaussianProcessKolmogorov

end

end OSforGFF
