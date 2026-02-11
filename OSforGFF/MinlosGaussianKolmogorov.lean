import OSforGFF.GaussianProcessKolmogorov
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

/-!
# Gaussian cylindrical measure via Kolmogorov extension (pre-Mìnlos)

This file is a **Minlos-pipeline** step:

Given a linear map `T : E →ₗ[ℝ] H` into a real inner product space, we form the covariance kernel
\[
K(f,g) = \langle Tf, Tg\rangle.
\]
Kolmogorov extension (already implemented in `OSforGFF.GaussianProcessKolmogorov`) then gives a
probability measure on the product space `E → ℝ` whose finite-dimensional marginals are centered
Gaussians with covariance given by `K`.

At this stage we only construct the measure on the **product space**; descending to a measure on
`WeakDual ℝ E` is exactly the hard step of Minlos, handled elsewhere.
-/

open scoped BigOperators NNReal ENNReal InnerProductSpace RealInnerProductSpace MatrixOrder

open MeasureTheory Complex Matrix

namespace OSforGFF

noncomputable section

namespace MinlosGaussianKolmogorov

open OSforGFF.GaussianProcessKolmogorov
open OSforGFF.FiniteDimGaussian
open WithLp (toLp ofLp)

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The covariance kernel induced by an embedding `T : E →ₗ[ℝ] H`. -/
def kernel (T : E →ₗ[ℝ] H) (f g : E) : ℝ := ⟪T f, T g⟫_ℝ

lemma covMatrix_kernel_eq_gram (T : E →ₗ[ℝ] H) (J : Finset E) :
    GaussianProcessKolmogorov.covMatrix (ι := E) (kernel T) J
      = Matrix.gram ℝ (fun j : J => T j.1) := by
  ext i j
  rfl

lemma covMatrix_kernel_posSemidef (T : E →ₗ[ℝ] H) (J : Finset E) :
    (GaussianProcessKolmogorov.covMatrix (ι := E) (kernel T) J).PosSemidef := by
  classical
  -- Reduce to the Gram-matrix lemma.
  simpa [covMatrix_kernel_eq_gram (T := T) (J := J)] using
    (Matrix.posSemidef_gram (𝕜 := ℝ) (E := H) (n := J) (fun j : J => T j.1))

/-- The Kolmogorov-extension Gaussian measure on the product space `E → ℝ` induced by `T`. -/
noncomputable def gaussianProcess (T : E →ₗ[ℝ] H) : Measure (E → ℝ) :=
  GaussianProcessKolmogorov.gaussianProcessOfKernel (ι := E) (K := kernel T)
    (fun J => covMatrix_kernel_posSemidef (T := T) J)

instance (T : E →ₗ[ℝ] H) : IsProbabilityMeasure (gaussianProcess (E := E) (H := H) T) := by
  classical
  -- `E` is nonempty because it has `0`.
  letI : Nonempty E := ⟨0⟩
  -- This is the instance from `GaussianProcessKolmogorov`.
  dsimp [gaussianProcess]
  infer_instance

/-- The one-dimensional characteristic functional of the Gaussian Kolmogorov measure:
for each `f : E`,
\[
  \int \exp(i\,\omega(f))\, d\mu(\omega) = \exp(-\tfrac12 \|T f\|^2).
\]

This is the cylindrical (finite-dimensional) content of the Gaussian Minlos statement; it does **not**
yet descend to a measure on `WeakDual ℝ E`. -/
theorem integral_exp_eval_eq (T : E →ₗ[ℝ] H) (f : E) :
    (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂(gaussianProcess (E := E) (H := H) T)) =
      Complex.exp (-(1 / 2 : ℂ) * (‖T f‖ ^ 2 : ℝ)) := by
  classical
  letI : Nonempty E := ⟨0⟩
  -- Work with the singleton marginal `{f}` on `EuclideanSpace ℝ {f}`.
  let J : Finset E := {f}
  have hfJ : f ∈ J := by simp [J]
  let j0 : J := ⟨f, hfJ⟩

  -- The map `ω ↦ toLp (J.restrict ω)` into `EuclideanSpace ℝ J`.
  let φ : (E → ℝ) → EuclideanSpace ℝ J :=
    fun ω => toLp (2 : ℝ≥0∞) (J.restrict ω)
  have hmeas_φ : Measurable φ := by
    -- `restrict` is measurable, and `toLp` is measurable.
    fun_prop

  -- Express the desired integral as `charFun` of the `EuclideanSpace` marginal at the basis vector.
  have h_as_charFun :
      (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂(gaussianProcess (E := E) (H := H) T)) =
        MeasureTheory.charFun ((gaussianProcess (E := E) (H := H) T).map φ)
          (EuclideanSpace.single j0 (1 : ℝ)) := by
    -- Unfold `charFun` and use `integral_map` along `φ`.
    let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
    let t0 : EuclideanSpace ℝ J := EuclideanSpace.single j0 (1 : ℝ)
    have hmeas_integrand :
        Measurable (fun x : EuclideanSpace ℝ J => Complex.exp (⟪x, t0⟫_ℝ * I)) := by
      fun_prop
    have hφ : AEMeasurable φ μ := hmeas_φ.aemeasurable
    have hfm : AEStronglyMeasurable (fun x : EuclideanSpace ℝ J => Complex.exp (⟪x, t0⟫_ℝ * I))
        (μ.map φ) :=
      hmeas_integrand.aestronglyMeasurable
    have hmap :
        (∫ x, Complex.exp (⟪x, t0⟫_ℝ * I) ∂(μ.map φ)) =
          ∫ ω, Complex.exp (⟪φ ω, t0⟫_ℝ * I) ∂μ := by
      simpa [μ, t0] using
        (MeasureTheory.integral_map (μ := μ) (φ := φ)
          (f := fun x : EuclideanSpace ℝ J => Complex.exp (⟪x, t0⟫_ℝ * I))
          (hφ := hφ) (hfm := hfm))
    -- Rewrite the RHS back on `E → ℝ` and simplify the inner product:
    -- `⟪toLp (J.restrict ω), single j0 1⟫ = (J.restrict ω) j0 = ω f`.
    rw [MeasureTheory.charFun_apply, hmap]
    -- Use commutativity in `ℂ` to rewrite `I * z` as `z * I`.
    simp [μ, t0, φ, J, j0, EuclideanSpace.inner_single_right, Finset.restrict_def,
      mul_assoc, mul_comm, mul_left_comm, mul_right_comm]

  -- Identify the `EuclideanSpace` marginal of `gaussianProcess` on `J` with `gaussianOfPosSemidef`.
  let Sigma : Matrix J J ℝ := GaussianProcessKolmogorov.covMatrix (ι := E) (kernel T) J
  have hSigma : Sigma.PosSemidef := covMatrix_kernel_posSemidef (T := T) J
  let μEuc : Measure (EuclideanSpace ℝ J) := gaussianOfPosSemidef (n := J) Sigma hSigma

  have hproj :
      ((gaussianProcess (E := E) (H := H) T).map (fun ω : E → ℝ => J.restrict ω)) =
        GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J hSigma := by
    simpa [gaussianProcess, GaussianProcessKolmogorov.gaussianFamily,
      GaussianProcessKolmogorov.gaussianFiniteLaw] using
        (GaussianProcessKolmogorov.isProjectiveLimit_gaussianProcessOfKernel
          (ι := E) (K := kernel T) (hK := fun J => covMatrix_kernel_posSemidef (T := T) J) J)

  have h_euclidean_marginal :
      ((gaussianProcess (E := E) (H := H) T).map φ) = μEuc := by
    -- First map by restriction to `J`, then by `toLp` to `EuclideanSpace`.
    have hmeas_restrict : Measurable (fun ω : E → ℝ => J.restrict ω) := by fun_prop
    have hmeas_toLp : Measurable (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J) := by
      simpa using (WithLp.measurable_toLp (p := (2 : ℝ≥0∞)) (X := J → ℝ))
    -- `map φ = map toLp (map restrict μ)`
    have hmapφ :
        ((gaussianProcess (E := E) (H := H) T).map φ) =
          Measure.map (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J)
            (((gaussianProcess (E := E) (H := H) T).map (fun ω : E → ℝ => J.restrict ω))) := by
      -- `φ` is literally `toLp ∘ restrict`.
      -- We use `Measure.map_map` in the direction `map toLp (map restrict μ) = map (toLp ∘ restrict) μ`.
      simpa [φ, Function.comp] using
        (Measure.map_map (μ := gaussianProcess (E := E) (H := H) T) hmeas_toLp hmeas_restrict).symm
    -- Replace the restricted law by `gaussianFiniteLaw`, then simplify `toLp` after `ofLp`.
    -- `gaussianFiniteLaw = μEuc.map ofLp`, so mapping by `toLp` gives back `μEuc`.
    have hfinite :
        GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J hSigma =
          Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) μEuc := by
      rfl
    -- Finish.
    calc
      ((gaussianProcess (E := E) (H := H) T).map φ)
          = Measure.map (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J)
              (((gaussianProcess (E := E) (H := H) T).map (fun ω : E → ℝ => J.restrict ω))) := hmapφ
      _ = Measure.map (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J)
            (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J hSigma) := by
            simpa [hproj]
      _ = Measure.map (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J)
            (Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) μEuc) := by
            simpa [hfinite]
      _ = μEuc := by
            -- `toLp` is the inverse of `ofLp`.
            have hmeas_ofLp :
                Measurable (ofLp : EuclideanSpace ℝ J → (J → ℝ)) := by
              simpa using (WithLp.measurable_ofLp (p := (2 : ℝ≥0∞)) (X := J → ℝ))
            have hcomp :
                ((toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J) ∘
                    (ofLp : EuclideanSpace ℝ J → (J → ℝ))) = id := by
              funext x
              simpa using (WithLp.toLp_ofLp (p := (2 : ℝ≥0∞)) (x := x))
            -- Combine the two `map`s and simplify using `toLp_ofLp`.
            calc
              Measure.map (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J)
                  (Measure.map (ofLp : EuclideanSpace ℝ J → (J → ℝ)) μEuc)
                  =
                Measure.map
                    (((toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J) ∘
                        (ofLp : EuclideanSpace ℝ J → (J → ℝ)))) μEuc := by
                      simpa using (Measure.map_map (μ := μEuc) hmeas_toLp hmeas_ofLp)
              _ = Measure.map (id : EuclideanSpace ℝ J → EuclideanSpace ℝ J) μEuc := by
                    simpa [hcomp]
              _ = μEuc := by
                    simpa using (Measure.map_id (μ := μEuc))

  -- Apply the explicit characteristic function of `gaussianOfPosSemidef` and compute the quadratic form.
  have h_char :
      MeasureTheory.charFun ((gaussianProcess (E := E) (H := H) T).map φ)
          (EuclideanSpace.single j0 (1 : ℝ)) =
        Complex.exp (-(1 / 2 : ℂ) * (‖T f‖ ^ 2 : ℝ)) := by
    -- Rewrite using `h_euclidean_marginal`, then use `charFun_gaussianOfPosSemidef`.
    have hEuc :=
      (charFun_gaussianOfPosSemidef (n := J) Sigma hSigma (t := EuclideanSpace.single j0 (1 : ℝ)))
    -- Compute the quadratic form `⟪e_j, Σ e_j⟫ = Σ j0 j0 = ‖T f‖^2`.
    have hquad :
        ⟪EuclideanSpace.single j0 (1 : ℝ),
            (Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma)
              (EuclideanSpace.single j0 (1 : ℝ))⟫_ℝ =
          ‖T f‖ ^ 2 := by
      -- The diagonal entry is `Sigma j0 j0 = ⟪T f, T f⟫ = ‖T f‖^2`.
      have hSigma00 : Sigma j0 j0 = ‖T f‖ ^ 2 := by
        simp [Sigma, GaussianProcessKolmogorov.covMatrix, kernel, j0, inner_self_eq_norm_sq]
      -- First compute the `j0` coordinate of `(toEuclideanCLM Sigma) (single j0 1)`.
      have hcoord :
          ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ))) j0
            = Sigma j0 j0 := by
        -- Use `ofLp_toEuclideanCLM` and the fact that `ofLp (single j0 1) = Pi.single j0 1`.
        have hof :
            ofLp ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ))) =
              Sigma *ᵥ ofLp (EuclideanSpace.single j0 (1 : ℝ)) := by
          simpa using (Matrix.ofLp_toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma (EuclideanSpace.single j0 (1 : ℝ)))
        have hof0 :
            ofLp (EuclideanSpace.single j0 (1 : ℝ) : EuclideanSpace ℝ J) = Pi.single j0 (1 : ℝ) := by
          simpa using (EuclideanSpace.ofLp_single (ι := J) (𝕜 := ℝ) j0 (1 : ℝ))
        -- Evaluate at `j0`, and use `mulVec_single_one`.
        have h' :
            (ofLp ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ)))) j0
              = (Sigma *ᵥ (Pi.single j0 (1 : ℝ))) j0 := by
          simpa [hof0] using congrArg (fun v => v j0) hof
        -- `Sigma *ᵥ Pi.single j0 1 = Sigma.col j0`, so the `j0` coordinate is `Sigma j0 j0`.
        simpa using (by
          -- provide decidable equality for the simp lemma
          classical
          simpa [Matrix.mulVec_single_one] using h')
      -- Now use `inner_single_left` to pick out that coordinate.
      -- Over `ℝ`, `conj` is the identity and `conj (1) = 1`.
      have : ⟪EuclideanSpace.single j0 (1 : ℝ),
            (Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ))⟫_ℝ
          = ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ))) j0 := by
        simpa using (EuclideanSpace.inner_single_left (ι := J) (𝕜 := ℝ) j0 (1 : ℝ)
          ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ))))
      simpa [this, hcoord, hSigma00]
    -- Combine.
    simpa [h_euclidean_marginal, μEuc, hquad] using hEuc

  -- Finish.
  simpa [h_as_charFun] using h_char

end MinlosGaussianKolmogorov

end

end OSforGFF
