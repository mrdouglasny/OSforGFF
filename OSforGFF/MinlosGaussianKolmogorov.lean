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
  simpa [covMatrix_kernel_eq_gram (T := T) (J := J)] using
    (Matrix.posSemidef_gram (𝕜 := ℝ) (E := H) (n := J) (fun j : J => T j.1))

/-- The Kolmogorov-extension Gaussian measure on the product space `E → ℝ` induced by `T`. -/
noncomputable def gaussianProcess (T : E →ₗ[ℝ] H) : Measure (E → ℝ) :=
  GaussianProcessKolmogorov.gaussianProcessOfKernel (ι := E) (K := kernel T)
    (fun J => covMatrix_kernel_posSemidef (T := T) J)

instance (T : E →ₗ[ℝ] H) : IsProbabilityMeasure (gaussianProcess (E := E) (H := H) T) := by
  letI : Nonempty E := ⟨0⟩
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
  letI : Nonempty E := ⟨0⟩
  let J : Finset E := {f}
  have hfJ : f ∈ J := by simp [J]
  let j0 : J := ⟨f, hfJ⟩
  let φ : (E → ℝ) → EuclideanSpace ℝ J :=
    fun ω => toLp (2 : ℝ≥0∞) (J.restrict ω)
  have hmeas_φ : Measurable φ := by
    fun_prop
  have h_as_charFun :
      (∫ ω, Complex.exp (I * ((ω f : ℝ) : ℂ)) ∂(gaussianProcess (E := E) (H := H) T)) =
        MeasureTheory.charFun ((gaussianProcess (E := E) (H := H) T).map φ)
          (EuclideanSpace.single j0 (1 : ℝ)) := by
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
    rw [MeasureTheory.charFun_apply, hmap]
    simp [μ, t0, φ, J, j0, EuclideanSpace.inner_single_right, Finset.restrict_def,
      mul_assoc, mul_comm, mul_left_comm, mul_right_comm]
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
    have hmeas_restrict : Measurable (fun ω : E → ℝ => J.restrict ω) := by fun_prop
    have hmeas_toLp : Measurable (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J) := by
      simpa using (WithLp.measurable_toLp (p := (2 : ℝ≥0∞)) (X := J → ℝ))
    have hmapφ :
        ((gaussianProcess (E := E) (H := H) T).map φ) =
          Measure.map (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J)
            (((gaussianProcess (E := E) (H := H) T).map (fun ω : E → ℝ => J.restrict ω))) := by
      simpa [φ, Function.comp] using
        (Measure.map_map (μ := gaussianProcess (E := E) (H := H) T) hmeas_toLp hmeas_restrict).symm
    have hfinite :
        GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J hSigma =
          Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) μEuc := by
      rfl
    calc
      ((gaussianProcess (E := E) (H := H) T).map φ)
          = Measure.map (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J)
              (((gaussianProcess (E := E) (H := H) T).map (fun ω : E → ℝ => J.restrict ω))) := hmapφ
      _ = Measure.map (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J)
            (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J hSigma) := by
            simp [hproj]
      _ = Measure.map (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J)
            (Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) μEuc) := by
            simp [hfinite]
      _ = μEuc := by
            have hmeas_ofLp :
                Measurable (ofLp : EuclideanSpace ℝ J → (J → ℝ)) := by
              simpa using (WithLp.measurable_ofLp (p := (2 : ℝ≥0∞)) (X := J → ℝ))
            have hcomp :
                ((toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J) ∘
                    (ofLp : EuclideanSpace ℝ J → (J → ℝ))) = id := by
              funext x
              simp
            calc
              Measure.map (toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J)
                  (Measure.map (ofLp : EuclideanSpace ℝ J → (J → ℝ)) μEuc)
                  =
                Measure.map
                    (((toLp (2 : ℝ≥0∞) : (J → ℝ) → EuclideanSpace ℝ J) ∘
                        (ofLp : EuclideanSpace ℝ J → (J → ℝ)))) μEuc := by
                      simpa using (Measure.map_map (μ := μEuc) hmeas_toLp hmeas_ofLp)
              _ = Measure.map (id : EuclideanSpace ℝ J → EuclideanSpace ℝ J) μEuc := by
                    simp [hcomp]
              _ = μEuc := by
                    simp
  have h_char :
      MeasureTheory.charFun ((gaussianProcess (E := E) (H := H) T).map φ)
          (EuclideanSpace.single j0 (1 : ℝ)) =
        Complex.exp (-(1 / 2 : ℂ) * (‖T f‖ ^ 2 : ℝ)) := by
    have hEuc :=
      (charFun_gaussianOfPosSemidef (n := J) Sigma hSigma (t := EuclideanSpace.single j0 (1 : ℝ)))
    have hquad :
        ⟪EuclideanSpace.single j0 (1 : ℝ),
            (Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma)
              (EuclideanSpace.single j0 (1 : ℝ))⟫_ℝ =
          ‖T f‖ ^ 2 := by
      have hSigma00 : Sigma j0 j0 = ‖T f‖ ^ 2 := by
        simp [Sigma, GaussianProcessKolmogorov.covMatrix, kernel, j0, inner_self_eq_norm_sq]
      have hcoord :
          ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ))) j0
            = Sigma j0 j0 := by
        have hof :
            ofLp ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ))) =
              Sigma *ᵥ ofLp (EuclideanSpace.single j0 (1 : ℝ)) := by
          simp
        have hof0 :
            ofLp (EuclideanSpace.single j0 (1 : ℝ) : EuclideanSpace ℝ J) = Pi.single j0 (1 : ℝ) := by
          simp
        have h' :
            (ofLp ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ)))) j0
              = (Sigma *ᵥ (Pi.single j0 (1 : ℝ))) j0 := by
          simp
        simp
      have : ⟪EuclideanSpace.single j0 (1 : ℝ),
            (Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ))⟫_ℝ
          = ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ))) j0 := by
        simpa using (EuclideanSpace.inner_single_left (ι := J) (𝕜 := ℝ) j0 (1 : ℝ)
          ((Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma) (EuclideanSpace.single j0 (1 : ℝ))))
      simp [this, hcoord, hSigma00]
    simpa [h_euclidean_marginal, μEuc, hquad] using hEuc
  simpa [h_as_charFun] using h_char

end MinlosGaussianKolmogorov

end

end OSforGFF
