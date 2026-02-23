/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.GaussianProcessKolmogorov
import OSforGFF.GaussianProcessKolmogorovIsGaussian
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.MeasureTheory.Measure.Dirac

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

Cylindrical (finite-dimensional) content of the Gaussian Minlos statement; it does **not**
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
      mul_comm]
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
        simp [Sigma, GaussianProcessKolmogorov.covMatrix, kernel, j0]
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

/-!
## (A) Almost-sure linearity of sample paths

Under the Kolmogorov Gaussian-process measure on `E → ℝ` induced by a linear embedding `T`,
the coordinate process `ω ↦ ω f` is jointly Gaussian with covariance `kernel T`.
In particular, the additivity and homogeneity defects have variance `0`, hence vanish a.s.

These are purely **finite-dimensional** consequences of the construction and do not use Minlos.
-/

section AlmostSureLinearity

open scoped RealInnerProductSpace

variable (T : E →ₗ[ℝ] H)

lemma map_restrict_eq_gaussianFiniteLaw (J : Finset E) :
    (gaussianProcess (E := E) (H := H) T).map (fun ω : E → ℝ => J.restrict ω) =
      GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J
        (covMatrix_kernel_posSemidef (T := T) J) := by
  simpa [gaussianProcess, GaussianProcessKolmogorov.gaussianFamily,
    GaussianProcessKolmogorov.gaussianFiniteLaw] using
      (GaussianProcessKolmogorov.isProjectiveLimit_gaussianProcessOfKernel
        (ι := E) (K := kernel T) (hK := fun J => covMatrix_kernel_posSemidef (T := T) J) J)

/-- Under the Kolmogorov Gaussian process measure, sample paths are additive a.s. -/
theorem ae_eval_add (f g : E) :
    (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T), ω (f + g) = ω f + ω g) := by
  classical
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  let J : Finset E := ({f, g, f + g} : Finset E)
  have hfJ : f ∈ J := by simp [J]
  have hgJ : g ∈ J := by simp [J]
  have hfgJ : f + g ∈ J := by simp [J]
  let jF : J := ⟨f, hfJ⟩
  let jG : J := ⟨g, hgJ⟩
  let jFG : J := ⟨f + g, hfgJ⟩
  let Lfun : (J → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) jFG)
      - (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) jF)
      - (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) jG)
  have hLfun_apply (x : J → ℝ) : Lfun x = x jFG - x jF - x jG := by
    simp [Lfun, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  let D : (E → ℝ) → ℝ := fun ω => ω (f + g) - ω f - ω g
  have hD : D = fun ω => Lfun (J.restrict ω) := by
    funext ω
    simp [D, hLfun_apply, Finset.restrict_def, jF, jG, jFG]
  have hmapJ :
      μ.map (fun ω : E → ℝ => J.restrict ω) =
        GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J
          (covMatrix_kernel_posSemidef (T := T) J) := by
    simpa [μ] using map_restrict_eq_gaussianFiniteLaw (E := E) (H := H) T J
  have hmeas_restrict : Measurable (fun ω : E → ℝ => J.restrict ω) := by
    fun_prop
  have hmeas_Lfun : Measurable Lfun := by
    have hproj_meas (j : J) : Measurable (fun x : J → ℝ => x j) := by
      simpa using (measurable_pi_apply j)
    have : (fun x : J → ℝ => Lfun x) =
        fun x => x jFG - x jF - x jG := by
      funext x; exact hLfun_apply x
    simpa [this, sub_eq_add_neg] using
      ((hproj_meas jFG).sub (hproj_meas jF)).sub (hproj_meas jG)
  have hmapD :
      μ.map D = (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J
          (covMatrix_kernel_posSemidef (T := T) J)).map Lfun := by
    rw [hD]
    calc
      μ.map (fun ω : E → ℝ => Lfun (J.restrict ω)) =
          (μ.map (fun ω : E → ℝ => J.restrict ω)).map (Lfun : (J → ℝ) → ℝ) := by
            have hm :
                (μ.map (fun ω : E → ℝ => J.restrict ω)).map (Lfun : (J → ℝ) → ℝ) =
                  μ.map ((Lfun : (J → ℝ) → ℝ) ∘ fun ω : E → ℝ => J.restrict ω) := by
              simpa using (Measure.map_map (μ := μ) hmeas_Lfun hmeas_restrict)
            simpa [Function.comp] using hm.symm
      _ = (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J
            (covMatrix_kernel_posSemidef (T := T) J)).map Lfun := by
            simp [hmapJ]
  let Sigma : Matrix J J ℝ := GaussianProcessKolmogorov.covMatrix (ι := E) (kernel T) J
  have hSigma : Sigma.PosSemidef := covMatrix_kernel_posSemidef (T := T) J
  let μEuc : Measure (EuclideanSpace ℝ J) := gaussianOfPosSemidef (n := J) Sigma hSigma
  have hfinite :
      GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J hSigma =
        Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) μEuc := rfl
  let v : EuclideanSpace ℝ J :=
    EuclideanSpace.single jFG (1 : ℝ) - EuclideanSpace.single jF (1 : ℝ) - EuclideanSpace.single jG (1 : ℝ)
  let Leuc : EuclideanSpace ℝ J →L[ℝ] ℝ := (innerSL ℝ v)
  have hLeuc (x : EuclideanSpace ℝ J) : Lfun (ofLp x) = Leuc x := by
    have hL : Lfun (ofLp x) = x jFG - x jF - x jG := by
      simp [hLfun_apply, jF, jG, jFG]
    have hE : Leuc x = x jFG - x jF - x jG := by
      have : Leuc x = ⟪x, v⟫_ℝ := by simp [Leuc, real_inner_comm]
      calc
        Leuc x = ⟪x, v⟫_ℝ := this
        _ = ⟪x, EuclideanSpace.single jFG (1 : ℝ)⟫_ℝ
              - ⟪x, EuclideanSpace.single jF (1 : ℝ)⟫_ℝ
              - ⟪x, EuclideanSpace.single jG (1 : ℝ)⟫_ℝ := by
              simp [v, sub_eq_add_neg, inner_add_right]
        _ = x jFG - x jF - x jG := by
              simp [EuclideanSpace.inner_single_right, sub_eq_add_neg, add_comm, add_left_comm]
    simpa [hE] using hL
  let A : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J :=
    Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma
  have hmulVec_v : Sigma *ᵥ (ofLp v) = 0 := by
    ext j
    have hv_ofLp :
        ofLp v =
          (Pi.single jFG (1 : ℝ) - Pi.single jF (1 : ℝ) - Pi.single jG (1 : ℝ)) := by
      simp [v, sub_eq_add_neg, add_assoc]
    have hcoord :
        (Sigma *ᵥ ofLp v) j =
          kernel T j.1 (f + g) - kernel T j.1 f - kernel T j.1 g := by
      simp [hv_ofLp, Sigma, GaussianProcessKolmogorov.covMatrix,
        Matrix.mulVec_add, Matrix.mulVec_neg, kernel, jF, jG, jFG,
        sub_eq_add_neg, add_assoc]
    have hadd : kernel T j.1 (f + g) = kernel T j.1 f + kernel T j.1 g := by
      simp [kernel, LinearMap.map_add, inner_add_right]
    simp [hcoord, hadd, sub_eq_add_neg, add_left_comm, add_comm]
  have hAv : A v = 0 := by
    have hinj : Function.Injective (ofLp : EuclideanSpace ℝ J → J → ℝ) := by
      intro x y hxy
      have := congrArg (toLp (2 : ℝ≥0∞)) hxy
      simpa using this
    apply hinj
    have : ofLp (A v) = Sigma *ᵥ ofLp v := by simp [A]
    simpa [hmulVec_v] using this
  have hquad : ⟪v, A v⟫_ℝ = 0 := by simp [hAv]
  have hpush_dirac :
      (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J hSigma).map Lfun =
        Measure.dirac 0 := by
    have hmeas_ofLp : Measurable (ofLp : EuclideanSpace ℝ J → J → ℝ) := by fun_prop
    have hmeas_Lfun' : Measurable Lfun := hmeas_Lfun
    have hmap :
        (Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) μEuc).map Lfun =
          μEuc.map Leuc := by
      have hcomp : (fun x : EuclideanSpace ℝ J => Lfun (ofLp x)) = fun x => Leuc x := by
        funext x; exact hLeuc x
      calc
        (Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) μEuc).map (Lfun : (J → ℝ) → ℝ) =
            μEuc.map ((Lfun : (J → ℝ) → ℝ) ∘ (ofLp : EuclideanSpace ℝ J → J → ℝ)) := by
              simpa using (Measure.map_map (μ := μEuc) hmeas_Lfun' hmeas_ofLp)
        _ = μEuc.map (fun x => Leuc x) := by
              have hcomp' :
                  ((Lfun : (J → ℝ) → ℝ) ∘ (ofLp : EuclideanSpace ℝ J → J → ℝ)) =
                    (fun x => Leuc x) := by
                funext x; simpa [Function.comp] using (hLeuc x)
              simp [hcomp']
        _ = μEuc.map Leuc := by rfl
    have hchar :
        MeasureTheory.charFun (μEuc.map Leuc) = MeasureTheory.charFun (Measure.dirac (0 : ℝ)) := by
      funext t
      have hmap_char :=
        charFun_map_continuousLinearMap (μ := μEuc) (L := Leuc) (t := (t : ℝ))
      have hadj : Leuc.adjoint t = t • v := by
        simpa [Leuc] using congrArg (fun L => L t)
          (ContinuousLinearMap.adjoint_innerSL_apply (𝕜 := ℝ) (x := v))
      have hAt : A (t • v) = 0 := by
        simp [map_smul, hAv]
      have hcf1 : MeasureTheory.charFun μEuc (t • v) = 1 := by
        have hsmulAv : t • A v = 0 := by
          simpa [hAt] using (A.map_smul t v).symm
        have hinner0' : ⟪t • v, t • A v⟫_ℝ = 0 := by simp [hsmulAv]
        have hcf :
            MeasureTheory.charFun μEuc (t • v) =
              Complex.exp (-(1 / 2 : ℂ) * ⟪t • v, A (t • v)⟫_ℝ) := by
          simpa [μEuc, A] using
            (charFun_gaussianOfPosSemidef (n := J) Sigma hSigma (t := (t • v)))
        simpa [hinner0'] using hcf
      calc
        MeasureTheory.charFun (μEuc.map Leuc) t
            = MeasureTheory.charFun μEuc (Leuc.adjoint t) := by simp [hmap_char]
        _ = MeasureTheory.charFun μEuc (t • v) := by simp [hadj]
        _ = 1 := hcf1
        _ = MeasureTheory.charFun (Measure.dirac (0 : ℝ)) t := by
              simp [MeasureTheory.charFun_dirac]
    have : μEuc.map Leuc = Measure.dirac (0 : ℝ) :=
      MeasureTheory.Measure.ext_of_charFun (μ := μEuc.map Leuc) (ν := Measure.dirac (0 : ℝ)) hchar
    simpa [hfinite, hmap] using this
  have hmapD' : μ.map D = Measure.dirac 0 := by
    calc
      μ.map D =
          (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J
            (covMatrix_kernel_posSemidef (T := T) J)).map Lfun := hmapD
      _ = (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J hSigma).map Lfun := by
            simp
      _ = Measure.dirac 0 := hpush_dirac
  have hD_meas : Measurable D := by
    have hf : Measurable (fun ω : E → ℝ => ω f) := by simpa using (measurable_pi_apply f)
    have hg : Measurable (fun ω : E → ℝ => ω g) := by simpa using (measurable_pi_apply g)
    have hfg : Measurable (fun ω : E → ℝ => ω (f + g)) := by
      simpa using (measurable_pi_apply (f + g))
    simpa [D, sub_eq_add_neg] using (hfg.sub hf).sub hg
  have hmeas0 : MeasurableSet ({0} : Set ℝ) := measurableSet_singleton 0
  have hpre : μ (D ⁻¹' ({0} : Set ℝ)) = 1 := by
    have h0 := congrArg (fun ν : Measure ℝ => ν ({0} : Set ℝ)) hmapD'
    simpa [Measure.map_apply hD_meas hmeas0] using h0
  have hAE : ∀ᵐ ω ∂μ, D ω = 0 := by
    have hmeas_set : MeasurableSet (D ⁻¹' ({0} : Set ℝ)) := by
      exact hD_meas hmeas0
    have hcompl : μ (D ⁻¹' ({0} : Set ℝ))ᶜ = 0 := by
      have hμuniv : μ Set.univ = 1 := by
        simp [μ]
      simpa [hμuniv, hpre] using (measure_compl hmeas_set (measure_ne_top μ _))
    have : D ⁻¹' ({0} : Set ℝ) ∈ MeasureTheory.ae μ := by
      exact (MeasureTheory.mem_ae_iff).2 (by simpa [hmeas_set] using hcompl)
    filter_upwards [this] with ω hω
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hω
  filter_upwards [hAE] with ω hω
  have : ω (f + g) - ω f - ω g = 0 := by simpa [D] using hω
  linarith

/-- Under the Kolmogorov Gaussian process measure, sample paths are ℝ-homogeneous a.s. -/
theorem ae_eval_smul (c : ℝ) (f : E) :
    (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T), ω (c • f) = c • (ω f)) := by
  classical
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  let J : Finset E := ({f, c • f} : Finset E)
  have hfJ : f ∈ J := by simp [J]
  have hcfJ : c • f ∈ J := by simp [J]
  let jF : J := ⟨f, hfJ⟩
  let jCF : J := ⟨c • f, hcfJ⟩
  let Lfun : (J → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) jCF)
      - c • (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : J => ℝ) jF)
  have hLfun_apply (x : J → ℝ) : Lfun x = x jCF - c • x jF := by
    simp [Lfun, sub_eq_add_neg]
  let D : (E → ℝ) → ℝ := fun ω => ω (c • f) - c • ω f
  have hD : D = fun ω => Lfun (J.restrict ω) := by
    funext ω
    simp [D, hLfun_apply, Finset.restrict_def, jF, jCF]
  have hmapJ :
      μ.map (fun ω : E → ℝ => J.restrict ω) =
        GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J
          (covMatrix_kernel_posSemidef (T := T) J) := by
    simpa [μ] using map_restrict_eq_gaussianFiniteLaw (E := E) (H := H) T J
  have hmeas_restrict : Measurable (fun ω : E → ℝ => J.restrict ω) := by
    fun_prop
  have hmeas_Lfun : Measurable Lfun := by
    have hproj_meas (j : J) : Measurable (fun x : J → ℝ => x j) := by
      simpa using (measurable_pi_apply j)
    have : (fun x : J → ℝ => Lfun x) = fun x => x jCF - c • x jF := by
      funext x; exact hLfun_apply x
    simpa [this, sub_eq_add_neg] using (hproj_meas jCF).sub ((hproj_meas jF).const_smul c)
  have hmapD :
      μ.map D =
        (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J
          (covMatrix_kernel_posSemidef (T := T) J)).map Lfun := by
    rw [hD]
    calc
      μ.map (fun ω : E → ℝ => Lfun (J.restrict ω)) =
          (μ.map (fun ω : E → ℝ => J.restrict ω)).map (Lfun : (J → ℝ) → ℝ) := by
            have hm :
                (μ.map (fun ω : E → ℝ => J.restrict ω)).map (Lfun : (J → ℝ) → ℝ) =
                  μ.map ((Lfun : (J → ℝ) → ℝ) ∘ fun ω : E → ℝ => J.restrict ω) := by
              simpa using (Measure.map_map (μ := μ) hmeas_Lfun hmeas_restrict)
            simpa [Function.comp] using hm.symm
      _ = (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J
            (covMatrix_kernel_posSemidef (T := T) J)).map Lfun := by
            simp [hmapJ]
  let Sigma : Matrix J J ℝ := GaussianProcessKolmogorov.covMatrix (ι := E) (kernel T) J
  have hSigma : Sigma.PosSemidef := covMatrix_kernel_posSemidef (T := T) J
  let μEuc : Measure (EuclideanSpace ℝ J) := gaussianOfPosSemidef (n := J) Sigma hSigma
  have hfinite :
      GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J hSigma =
        Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) μEuc := rfl
  let v : EuclideanSpace ℝ J := EuclideanSpace.single jCF (1 : ℝ) - EuclideanSpace.single jF c
  let Leuc : EuclideanSpace ℝ J →L[ℝ] ℝ := (innerSL ℝ v)

  have hLeuc (x : EuclideanSpace ℝ J) : Lfun (ofLp x) = Leuc x := by
    have hL : Lfun (ofLp x) = x jCF - c • x jF := by
      simp [hLfun_apply, jF, jCF]
    have hE : Leuc x = x jCF - c • x jF := by
      have : Leuc x = ⟪x, v⟫_ℝ := by simp [Leuc, real_inner_comm]
      calc
        Leuc x = ⟪x, v⟫_ℝ := this
        _ = ⟪x, EuclideanSpace.single jCF (1 : ℝ)⟫_ℝ - ⟪x, EuclideanSpace.single jF c⟫_ℝ := by
              simp [v, inner_sub_right]
        _ = x jCF - c • x jF := by
              simp [EuclideanSpace.inner_single_right, sub_eq_add_neg]
    simpa [hE] using hL
  let A : EuclideanSpace ℝ J →L[ℝ] EuclideanSpace ℝ J :=
    Matrix.toEuclideanCLM (n := J) (𝕜 := ℝ) Sigma
  have hmulVec_v : Sigma *ᵥ (ofLp v) = 0 := by
    ext j
    have hv_ofLp : ofLp v = (Pi.single jCF (1 : ℝ) - Pi.single jF c) := by
      simp [v, sub_eq_add_neg]
    have hcoord :
        (Sigma *ᵥ ofLp v) j = kernel T j.1 (c • f) - c * kernel T j.1 f := by
      simp [hv_ofLp, Sigma, GaussianProcessKolmogorov.covMatrix,
        Matrix.mulVec_add, Matrix.mulVec_neg, Matrix.mulVec_single, kernel, jF, jCF,
        sub_eq_add_neg]
    have hsmul : kernel T j.1 (c • f) = c * kernel T j.1 f := by
      simp [kernel, inner_smul_right]
    simp [hcoord, hsmul]
  have hAv : A v = 0 := by
    have hinj : Function.Injective (ofLp : EuclideanSpace ℝ J → J → ℝ) := by
      intro x y hxy
      have := congrArg (toLp (2 : ℝ≥0∞)) hxy
      simpa using this
    apply hinj
    have : ofLp (A v) = Sigma *ᵥ ofLp v := by simp [A]
    simpa [hmulVec_v] using this
  have hpush_dirac :
      (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J hSigma).map Lfun =
        Measure.dirac 0 := by
    have hmeas_ofLp : Measurable (ofLp : EuclideanSpace ℝ J → J → ℝ) := by fun_prop
    have hmap :
        (Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) μEuc).map Lfun = μEuc.map Leuc := by
      have hcomp' :
          ((Lfun : (J → ℝ) → ℝ) ∘ (ofLp : EuclideanSpace ℝ J → J → ℝ)) = (fun x => Leuc x) := by
        funext x; simpa [Function.comp] using (hLeuc x)
      calc
        (Measure.map (ofLp : EuclideanSpace ℝ J → J → ℝ) μEuc).map (Lfun : (J → ℝ) → ℝ) =
            μEuc.map ((Lfun : (J → ℝ) → ℝ) ∘ (ofLp : EuclideanSpace ℝ J → J → ℝ)) := by
              simpa using (Measure.map_map (μ := μEuc) hmeas_Lfun hmeas_ofLp)
        _ = μEuc.map (fun x => Leuc x) := by simp [hcomp']
        _ = μEuc.map Leuc := rfl
    have hchar :
        MeasureTheory.charFun (μEuc.map Leuc) = MeasureTheory.charFun (Measure.dirac (0 : ℝ)) := by
      funext t
      have hmap_char := charFun_map_continuousLinearMap (μ := μEuc) (L := Leuc) (t := (t : ℝ))
      have hadj : Leuc.adjoint t = t • v := by
        simpa [Leuc] using congrArg (fun L => L t)
          (ContinuousLinearMap.adjoint_innerSL_apply (𝕜 := ℝ) (x := v))
      have hAt : A (t • v) = 0 := by
        simp [map_smul, hAv]
      have hsmulAv : t • A v = 0 := by
        simpa [hAt] using (A.map_smul t v).symm
      have hinner0' : ⟪t • v, t • A v⟫_ℝ = 0 := by simp [hsmulAv]
      have hcf1 : MeasureTheory.charFun μEuc (t • v) = 1 := by
        have hcf :
            MeasureTheory.charFun μEuc (t • v) =
              Complex.exp (-(1 / 2 : ℂ) * ⟪t • v, A (t • v)⟫_ℝ) := by
          simpa [μEuc, A] using
            (charFun_gaussianOfPosSemidef (n := J) Sigma hSigma (t := (t • v)))
        simpa [hinner0'] using hcf
      calc
        MeasureTheory.charFun (μEuc.map Leuc) t = MeasureTheory.charFun μEuc (Leuc.adjoint t) := by
              simp [hmap_char]
        _ = MeasureTheory.charFun μEuc (t • v) := by simp [hadj]
        _ = 1 := hcf1
        _ = MeasureTheory.charFun (Measure.dirac (0 : ℝ)) t := by simp [MeasureTheory.charFun_dirac]
    have : μEuc.map Leuc = Measure.dirac (0 : ℝ) :=
      MeasureTheory.Measure.ext_of_charFun (μ := μEuc.map Leuc) (ν := Measure.dirac (0 : ℝ)) hchar
    simpa [hfinite, hmap] using this
  have hmapD' : μ.map D = Measure.dirac 0 := by
    calc
      μ.map D =
          (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J
            (covMatrix_kernel_posSemidef (T := T) J)).map Lfun := hmapD
      _ = (GaussianProcessKolmogorov.gaussianFiniteLaw (ι := E) (kernel T) J hSigma).map Lfun := by
            simp
      _ = Measure.dirac 0 := hpush_dirac
  have hD_meas : Measurable D := by
    have hf : Measurable (fun ω : E → ℝ => ω f) := by simpa using (measurable_pi_apply f)
    have hcf : Measurable (fun ω : E → ℝ => ω (c • f)) := by
      simpa using (measurable_pi_apply (c • f))
    simpa [D, sub_eq_add_neg] using hcf.sub (hf.const_smul c)
  have hpre : μ (D ⁻¹' ({0} : Set ℝ)) = 1 := by
    have h0 := congrArg (fun ν : Measure ℝ => ν ({0} : Set ℝ)) hmapD'
    have hmeas0 : MeasurableSet ({0} : Set ℝ) := measurableSet_singleton 0
    simpa [Measure.map_apply hD_meas hmeas0] using h0
  have hAE : ∀ᵐ ω ∂μ, D ω = 0 := by
    have hmeas0 : MeasurableSet ({0} : Set ℝ) := measurableSet_singleton 0
    have hmeas_set : MeasurableSet (D ⁻¹' ({0} : Set ℝ)) := by exact hD_meas hmeas0
    have hcompl : μ (D ⁻¹' ({0} : Set ℝ))ᶜ = 0 := by
      have hμuniv : μ Set.univ = 1 := by simp [μ]
      simpa [hμuniv, hpre] using (measure_compl hmeas_set (measure_ne_top μ _))
    have : D ⁻¹' ({0} : Set ℝ) ∈ MeasureTheory.ae μ := by
      exact (MeasureTheory.mem_ae_iff).2 (by simpa [hmeas_set] using hcompl)
    filter_upwards [this] with ω hω
    simpa [Set.mem_preimage, Set.mem_singleton_iff] using hω
  filter_upwards [hAE] with ω hω
  have : ω (c • f) - c • ω f = 0 := by simpa [D] using hω
  linarith

/-!
### Countable families

For later use (when we pass to a countable dense subset / countable generating family), it is
convenient to have “simultaneous” almost-sure linearity statements over **countable** index types.
-/

/-- Additivity holds simultaneously on a countable family. -/
theorem ae_eval_add_all {ι : Type*} [Countable ι] (v : ι → E) :
    (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
      ∀ i j : ι, ω (v i + v j) = ω (v i) + ω (v j)) := by
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  have hpair :
      ∀ ij : ι × ι, (∀ᵐ ω ∂μ, ω (v ij.1 + v ij.2) = ω (v ij.1) + ω (v ij.2)) := by
    intro ij
    simpa [μ] using (ae_eval_add (E := E) (H := H) (T := T) (f := v ij.1) (g := v ij.2))
  have hall :
      (∀ᵐ ω ∂μ, ∀ ij : ι × ι, ω (v ij.1 + v ij.2) = ω (v ij.1) + ω (v ij.2)) :=
    (MeasureTheory.ae_all_iff (μ := μ)).2 hpair
  filter_upwards [hall] with ω hω
  intro i j
  simpa using hω (i, j)

/-- ℚ-homogeneity (viewed as ℝ-homogeneity along the cast `ℚ → ℝ`) holds simultaneously on a
countable family. -/
theorem ae_eval_smul_all_rat {ι : Type*} [Countable ι] (v : ι → E) :
    (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
      ∀ q : ℚ, ∀ i : ι, ω ((q : ℝ) • v i) = (q : ℝ) • (ω (v i))) := by
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  have hpair :
      ∀ qi : ℚ × ι, (∀ᵐ ω ∂μ, ω ((qi.1 : ℝ) • v qi.2) = (qi.1 : ℝ) • (ω (v qi.2))) := by
    intro qi
    simpa [μ] using (ae_eval_smul (E := E) (H := H) (T := T) (c := (qi.1 : ℝ)) (f := v qi.2))
  have hall :
      (∀ᵐ ω ∂μ, ∀ qi : ℚ × ι, ω ((qi.1 : ℝ) • v qi.2) = (qi.1 : ℝ) • (ω (v qi.2))) :=
    (MeasureTheory.ae_all_iff (μ := μ)).2 hpair
  filter_upwards [hall] with ω hω
  intro q i
  simpa using hω (q, i)

/-- The one-dimensional marginal `ω ↦ ω f` under the Kolmogorov Gaussian process measure is a
centered real Gaussian with variance `‖T f‖²`. -/
theorem map_eval_eq_gaussianReal (T : E →ₗ[ℝ] H) (f : E) :
    (gaussianProcess (E := E) (H := H) T).map (fun ω : E → ℝ => ω f) =
      ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖T f‖ ^ 2)) := by
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  let evalF : (E → ℝ) → ℝ := fun ω => ω f
  have hmeas_evalF : Measurable evalF := by
    simpa [evalF] using (measurable_pi_apply f)

  have hchar :
      MeasureTheory.charFun (μ.map evalF) = MeasureTheory.charFun
        (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖T f‖ ^ 2))) := by
    funext t
    have hcharL :
        MeasureTheory.charFun (μ.map evalF) t =
          Complex.exp (-(1 / 2 : ℂ) * ((t ^ 2) * (‖T f‖ ^ 2) : ℝ)) := by
      have hmeas_integrand : Measurable (fun x : ℝ => Complex.exp (t * x * I)) := by
        fun_prop
      have hAe_evalF : AEMeasurable evalF μ := hmeas_evalF.aemeasurable
      have hAS_integrand :
          AEStronglyMeasurable (fun x : ℝ => Complex.exp (t * x * I)) (μ.map evalF) :=
        hmeas_integrand.aestronglyMeasurable
      have hmap :
          (∫ x, Complex.exp (t * x * I) ∂(μ.map evalF)) =
            ∫ ω, Complex.exp (t * (evalF ω) * I) ∂μ := by
        simpa using
          (MeasureTheory.integral_map (μ := μ) (φ := evalF)
            (f := fun x : ℝ => Complex.exp (t * x * I)) (hφ := hAe_evalF) (hfm := hAS_integrand))
      have hAE_smul : ∀ᵐ ω ∂μ, ω (t • f) = t • ω f := by
        simpa [μ] using (ae_eval_smul (E := E) (H := H) (T := T) (c := t) (f := f))
      have hcongr :
          (fun ω : E → ℝ => Complex.exp (t * (evalF ω) * I)) =ᵐ[μ]
            (fun ω : E → ℝ => Complex.exp (I * ((ω (t • f) : ℝ) : ℂ))) := by
        filter_upwards [hAE_smul] with ω hω
        have ht : ω (t • f) = t * ω f := by simpa [smul_eq_mul] using hω
        calc
          Complex.exp (t * (evalF ω) * I)
              = Complex.exp (I * ((t * ω f : ℝ) : ℂ)) := by
                  simp [evalF, mul_comm, Complex.ofReal_mul]
          _ = Complex.exp (I * ((ω (t • f) : ℝ) : ℂ)) := by simp [ht]
      have hint :
          (∫ ω, Complex.exp (t * (evalF ω) * I) ∂μ) =
            (∫ ω, Complex.exp (I * ((ω (t • f) : ℝ) : ℂ)) ∂μ) := by
        refine MeasureTheory.integral_congr_ae ?_
        exact hcongr
      have hscaled :
          (∫ ω, Complex.exp (I * ((ω (t • f) : ℝ) : ℂ)) ∂μ) =
            Complex.exp (-(1 / 2 : ℂ) * (‖T (t • f)‖ ^ 2 : ℝ)) := by
        simpa [μ] using (integral_exp_eval_eq (E := E) (H := H) (T := T) (f := t • f))
      have hnorm :
          (‖T (t • f)‖ ^ 2 : ℝ) = (t ^ 2) * (‖T f‖ ^ 2) := by
        calc
          (‖T (t • f)‖ ^ 2 : ℝ) = (‖(t : ℝ) • T f‖ ^ 2 : ℝ) := by
            simp
          _ = ((‖(t : ℝ)‖ * ‖T f‖) ^ 2 : ℝ) := by simp [norm_smul]
          _ = ((|t| * ‖T f‖) ^ 2 : ℝ) := by simp [Real.norm_eq_abs]
          _ = (t ^ 2) * (‖T f‖ ^ 2) := by
            calc
              (|t| * ‖T f‖) ^ 2 = (|t| ^ 2) * (‖T f‖ ^ 2) := by
                simp [mul_pow]
              _ = (t ^ 2) * (‖T f‖ ^ 2) := by
                simp [sq_abs]
      have hchar' :
          MeasureTheory.charFun (μ.map evalF) t =
            Complex.exp (-(1 / 2 : ℂ) * (‖T (t • f)‖ ^ 2 : ℝ)) := by
        calc
          MeasureTheory.charFun (μ.map evalF) t =
              (∫ x, Complex.exp (t * x * I) ∂(μ.map evalF)) := by
                simp [MeasureTheory.charFun_apply_real]
          _ = (∫ ω, Complex.exp (t * (evalF ω) * I) ∂μ) := hmap
          _ = (∫ ω, Complex.exp (I * ((ω (t • f) : ℝ) : ℂ)) ∂μ) := hint
          _ = Complex.exp (-(1 / 2 : ℂ) * (‖T (t • f)‖ ^ 2 : ℝ)) := hscaled
      have hexp :
          Complex.exp (-(1 / 2 : ℂ) * (‖T (t • f)‖ ^ 2 : ℝ)) =
            Complex.exp (-(1 / 2 : ℂ) * ((t ^ 2) * (‖T f‖ ^ 2) : ℝ)) := by
        rw [hnorm]
      exact hchar'.trans hexp
    have hcharR :
        MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖T f‖ ^ 2))) t =
          Complex.exp (-(1 / 2 : ℂ) * ((t ^ 2) * (‖T f‖ ^ 2) : ℝ)) := by
      have h :=
        ProbabilityTheory.charFun_gaussianReal
          (μ := (0 : ℝ)) (v := Real.toNNReal (‖T f‖ ^ 2)) t
      have hv : ((Real.toNNReal (‖T f‖ ^ 2) : ℝ≥0) : ℝ) = (‖T f‖ ^ 2 : ℝ) :=
        Real.coe_toNNReal _ (sq_nonneg ‖T f‖)
      have h0 :
          MeasureTheory.charFun (ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖T f‖ ^ 2))) t =
            Complex.exp (-(Real.toNNReal (‖T f‖ ^ 2) : ℂ) * (t ^ 2 : ℝ) / 2) := by
        simpa [sub_eq_add_neg, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
      have hcoeff :
          ((Real.toNNReal (‖T f‖ ^ 2) : ℂ)) = ((‖T f‖ ^ 2 : ℝ) : ℂ) := by
        have : ((Real.toNNReal (‖T f‖ ^ 2) : ℝ≥0) : ℝ) = (‖T f‖ ^ 2 : ℝ) := hv
        exact_mod_cast this
      rw [h0]
      simp [div_eq_mul_inv, mul_comm]
    simp [hcharL, hcharR]

  exact MeasureTheory.Measure.ext_of_charFun
    (μ := μ.map evalF)
    (ν := ProbabilityTheory.gaussianReal 0 (Real.toNNReal (‖T f‖ ^ 2))) hchar

end AlmostSureLinearity


end MinlosGaussianKolmogorov

end

end OSforGFF
