import OSforGFF.MinlosGaussianSupport
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# `L²` evaluation operator for the Gaussian Kolmogorov measure

This file is a Minlos-pipeline component.  For the Kolmogorov Gaussian process measure
`gaussianProcess T` on the product space `E → ℝ`, we construct the canonical continuous linear
map

`BanachOfSeminorm (seminormFamily n) →L[ℝ] (E → ℝ) →₂[gaussianProcess T] ℝ`

obtained by extending the evaluation random variables `ω ↦ ω f` from `E` to the local Banach
completion.

The key point is the bound `‖ω ↦ ω f‖₂ ≤ (C : ℝ) * seminormFamily n f` coming from the variance
identity `Var[ω f] = ‖T f‖²` and a seminorm domination of `‖T ·‖`.
-/

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace ProbabilityTheory

namespace OSforGFF

noncomputable section

namespace MinlosGaussianSupport

open OSforGFF.MinlosGaussianKolmogorov
open OSforGFF.NuclearSpaceStd

-- We work with the seminorm-induced norm/topology on `E ⧸ seminormKer p` (used to form
-- `QuotBySeminorm` and its completion).  The generic quotient-module topology instance would clash
-- with this choice, so we disable it locally.
attribute [-instance] QuotientModule.Quotient.topologicalSpace

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

variable [NuclearSpaceStd E]

/-!
## The `L²`-valued evaluation map on `E`
-/

/-- The `L²` element corresponding to the evaluation random variable `ω ↦ ω f`. -/
noncomputable
def evalL2 (T : E →ₗ[ℝ] H) (f : E) :
    (E → ℝ) →₂[gaussianProcess (E := E) (H := H) T] ℝ :=
  (memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp)).toLp
    (fun ω : E → ℝ => ω f)

omit [TopologicalSpace E] [NuclearSpaceStd E] in
lemma evalL2_ae_eq (T : E →ₗ[ℝ] H) (f : E) :
    (evalL2 (E := E) (H := H) T f : (E → ℝ) → ℝ) =ᵐ[gaussianProcess (E := E) (H := H) T]
      (fun ω : E → ℝ => ω f) := by
  simpa [evalL2] using
    (MeasureTheory.MemLp.coeFn_toLp
      (μ := gaussianProcess (E := E) (H := H) T)
      (f := fun ω : E → ℝ => ω f)
      (hf := memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp)))

/-- The evaluation map `E →ₗ[ℝ] L²(gaussianProcess T)`. -/
noncomputable
def evalL2ₗ (T : E →ₗ[ℝ] H) :
    E →ₗ[ℝ] (E → ℝ) →₂[gaussianProcess (E := E) (H := H) T] ℝ where
  toFun f := evalL2 (E := E) (H := H) T f
  map_add' f g := by
    -- Use `MemLp.toLp_congr` and the a.s. additivity defect.
    let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
    have hAE :
        (fun ω : E → ℝ => ω (f + g)) =ᵐ[μ] fun ω : E → ℝ => ω f + ω g := by
      filter_upwards [ae_eval_add (E := E) (H := H) (T := T) f g] with ω hω
      simpa using hω
    have hcongr :
        (memLp_eval (E := E) (H := H) (T := T) (f + g) (p := (2 : ENNReal)) (by simp)).toLp
            (fun ω : E → ℝ => ω (f + g)) =
          ((memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp)).add
              (memLp_eval (E := E) (H := H) (T := T) g (p := (2 : ENNReal)) (by simp))).toLp
            (fun ω : E → ℝ => ω f + ω g) := by
      exact MeasureTheory.MemLp.toLp_congr
        (memLp_eval (E := E) (H := H) (T := T) (f + g) (p := (2 : ENNReal)) (by simp))
        ((memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp)).add
          (memLp_eval (E := E) (H := H) (T := T) g (p := (2 : ENNReal)) (by simp)))
        (by simpa [μ] using hAE)
    calc
      evalL2 (E := E) (H := H) T (f + g)
          =
        (memLp_eval (E := E) (H := H) (T := T) (f + g) (p := (2 : ENNReal)) (by simp)).toLp
          (fun ω : E → ℝ => ω (f + g)) := rfl
      _ =
        ((memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp)).add
            (memLp_eval (E := E) (H := H) (T := T) g (p := (2 : ENNReal)) (by simp))).toLp
          (fun ω : E → ℝ => ω f + ω g) := hcongr
      _ =
        (memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp)).toLp
            (fun ω : E → ℝ => ω f) +
          (memLp_eval (E := E) (H := H) (T := T) g (p := (2 : ENNReal)) (by simp)).toLp
            (fun ω : E → ℝ => ω g) := rfl
      _ = evalL2 (E := E) (H := H) T f + evalL2 (E := E) (H := H) T g := rfl
  map_smul' c f := by
    let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
    have hAE :
        (fun ω : E → ℝ => ω (c • f)) =ᵐ[μ] fun ω : E → ℝ => c • ω f := by
      filter_upwards [ae_eval_smul (E := E) (H := H) (T := T) (c := c) (f := f)] with ω hω
      simpa using hω
    have hcongr :
        (memLp_eval (E := E) (H := H) (T := T) (c • f) (p := (2 : ENNReal)) (by simp)).toLp
            (fun ω : E → ℝ => ω (c • f)) =
          ((memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp)).const_smul c).toLp
            (fun ω : E → ℝ => c • ω f) := by
      exact MeasureTheory.MemLp.toLp_congr
        (memLp_eval (E := E) (H := H) (T := T) (c • f) (p := (2 : ENNReal)) (by simp))
        ((memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp)).const_smul c)
        (by simpa [μ] using hAE)
    calc
      evalL2 (E := E) (H := H) T (c • f)
          =
        (memLp_eval (E := E) (H := H) (T := T) (c • f) (p := (2 : ENNReal)) (by simp)).toLp
          (fun ω : E → ℝ => ω (c • f)) := rfl
      _ =
        ((memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp)).const_smul c).toLp
          (fun ω : E → ℝ => c • ω f) := hcongr
      _ =
        c • (memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp)).toLp
              (fun ω : E → ℝ => ω f) := by
            simpa using (MeasureTheory.MemLp.toLp_const_smul (μ := μ)
              (c := c) (f := fun ω : E → ℝ => ω f)
              (hf := memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp)))
      _ = c • evalL2 (E := E) (H := H) T f := rfl

/-!
## `L²` norm control by seminorms
-/

omit [TopologicalSpace E] [NuclearSpaceStd E] in
theorem norm_evalL2_pow_two (T : E →ₗ[ℝ] H) (f : E) :
    ‖evalL2 (E := E) (H := H) T f‖ ^ 2 =
      ∫ ω, ((ω f : ℝ) ^ 2) ∂(gaussianProcess (E := E) (H := H) T) := by
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  have hnorm :
      ‖evalL2 (E := E) (H := H) T f‖ ^ 2 =
        ⟪evalL2 (E := E) (H := H) T f, evalL2 (E := E) (H := H) T f⟫ := by
    simp
  have h_ae :
      (fun ω : E → ℝ => (evalL2 (E := E) (H := H) T f ω : ℝ)) =ᵐ[μ] fun ω : E → ℝ => ω f := by
    simpa [μ] using (evalL2_ae_eq (E := E) (H := H) (T := T) (f := f))
  have h_ae_sq :
      (fun ω : E → ℝ => ((evalL2 (E := E) (H := H) T f ω : ℝ) ^ 2)) =ᵐ[μ]
        fun ω : E → ℝ => (ω f : ℝ) ^ 2 := by
    filter_upwards [h_ae] with ω hω
    simp [hω]
  calc
    ‖evalL2 (E := E) (H := H) T f‖ ^ 2
        = ⟪evalL2 (E := E) (H := H) T f, evalL2 (E := E) (H := H) T f⟫ := hnorm
    _ = ∫ ω : (E → ℝ), ⟪(evalL2 (E := E) (H := H) T f) ω, (evalL2 (E := E) (H := H) T f) ω⟫ ∂μ := by
          simpa [μ] using (MeasureTheory.L2.inner_def (𝕜 := ℝ) (E := ℝ)
            (μ := μ) (f := evalL2 (E := E) (H := H) T f) (g := evalL2 (E := E) (H := H) T f))
    _ = ∫ ω : (E → ℝ), ((evalL2 (E := E) (H := H) T f ω : ℝ) ^ 2) ∂μ := by
          refine integral_congr_ae ?_
          refine Filter.Eventually.of_forall (fun ω => ?_)
          simp [inner_self_eq_norm_sq_to_K, Real.norm_eq_abs]
    _ = ∫ ω : (E → ℝ), (ω f : ℝ) ^ 2 ∂μ := by
          exact integral_congr_ae h_ae_sq

omit [TopologicalSpace E] [NuclearSpaceStd E] in
theorem norm_evalL2_pow_two_eq_norm_T_pow_two (T : E →ₗ[ℝ] H) (f : E) :
    ‖evalL2 (E := E) (H := H) T f‖ ^ 2 = (‖T f‖ ^ 2 : ℝ) := by
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  have hmean : μ[(fun ω : E → ℝ => ω f)] = 0 := by
    simpa [μ] using (integral_eval_eq_zero (E := E) (H := H) (T := T) f)
  have hvar :
      Var[(fun ω : E → ℝ => ω f); μ] = (‖T f‖ ^ 2 : ℝ) := by
    simpa [μ] using (variance_eval_eq (E := E) (H := H) (T := T) f)
  have hAEm : AEMeasurable (fun ω : E → ℝ => ω f) μ :=
    (measurable_pi_apply f).aemeasurable
  have hvar_int :
      Var[(fun ω : E → ℝ => ω f); μ] = ∫ ω, ((ω f : ℝ) ^ 2) ∂μ := by
    simpa [hmean] using (ProbabilityTheory.variance_of_integral_eq_zero (μ := μ) hAEm hmean)
  calc
    ‖evalL2 (E := E) (H := H) T f‖ ^ 2
        = ∫ ω, ((ω f : ℝ) ^ 2) ∂μ := by
            simpa [μ] using (norm_evalL2_pow_two (E := E) (H := H) (T := T) f)
    _ = Var[(fun ω : E → ℝ => ω f); μ] := hvar_int.symm
    _ = (‖T f‖ ^ 2 : ℝ) := hvar

/-- `L²` norm control by a `NuclearSpaceStd` seminorm bound on `‖T ·‖`. -/
theorem norm_evalL2_le_of_le_seminormFamily (T : E →ₗ[ℝ] H) {n : ℕ} {C : ℝ≥0}
    (hle : (normSeminorm ℝ H).comp T ≤ C • (seminormFamily (E := E) n)) (f : E) :
    ‖evalL2 (E := E) (H := H) T f‖ ≤ (C : ℝ) * (seminormFamily (E := E) n) f := by
  have hTf : ‖T f‖ ≤ (C : ℝ) * (seminormFamily (E := E) n) f := by
    have := hle f
    simpa [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc] using this
  have hTf_sq :
      (‖T f‖ ^ 2 : ℝ) ≤ ((C : ℝ) * (seminormFamily (E := E) n) f) ^ 2 := by
    have hnonneg : (0 : ℝ) ≤ (C : ℝ) * (seminormFamily (E := E) n) f := by
      have : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast C.2
      exact mul_nonneg this (apply_nonneg _ _)
    simpa [pow_two] using (mul_le_mul hTf hTf (norm_nonneg _) hnonneg)
  have hsq :
      ‖evalL2 (E := E) (H := H) T f‖ ^ 2 ≤ ((C : ℝ) * (seminormFamily (E := E) n) f) ^ 2 := by
    simpa [norm_evalL2_pow_two_eq_norm_T_pow_two (E := E) (H := H) (T := T) (f := f)] using hTf_sq
  have hnonneg : (0 : ℝ) ≤ (C : ℝ) * (seminormFamily (E := E) n) f := by
    have : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast C.2
    exact mul_nonneg this (apply_nonneg _ _)
  exact le_of_sq_le_sq hsq hnonneg

theorem evalL2_eq_zero_of_seminormFamily_eq_zero (T : E →ₗ[ℝ] H) {n : ℕ} {C : ℝ≥0}
    (hle : (normSeminorm ℝ H).comp T ≤ C • (seminormFamily (E := E) n))
    {f : E} (hf0 : seminormFamily (E := E) n f = 0) :
    evalL2 (E := E) (H := H) T f = 0 := by
  have hnorm : ‖evalL2 (E := E) (H := H) T f‖ ≤ 0 := by
    simpa [hf0] using (norm_evalL2_le_of_le_seminormFamily (E := E) (H := H) (T := T)
      (n := n) (C := C) hle f)
  have : ‖evalL2 (E := E) (H := H) T f‖ = 0 :=
    le_antisymm hnorm (norm_nonneg _)
  simpa using (norm_eq_zero.mp this)

/-!
## Factoring through `QuotBySeminorm` and extending to `BanachOfSeminorm`
-/

open OSforGFF

/-- The `L²` evaluation map on the seminorm quotient `E ⧸ ker(seminormFamily n)`. -/
noncomputable
def evalL2QuotCLM (T : E →ₗ[ℝ] H) (n : ℕ) (C : ℝ≥0)
    (hle : (normSeminorm ℝ H).comp T ≤ C • (seminormFamily (E := E) n)) :
    QuotBySeminorm (E := E) (seminormFamily (E := E) n)
      →L[ℝ] (E → ℝ) →₂[gaussianProcess (E := E) (H := H) T] ℝ := by
  let p : Seminorm ℝ E := seminormFamily (E := E) n
  have hker : seminormKer (E := E) p ≤ LinearMap.ker (evalL2ₗ (E := E) (H := H) T) := by
    intro f hf
    have hf0 : p f = 0 := hf
    have : evalL2 (E := E) (H := H) T f = 0 :=
      evalL2_eq_zero_of_seminormFamily_eq_zero (E := E) (H := H) (T := T) (n := n) (C := C) hle hf0
    simpa [evalL2ₗ, evalL2] using this
  refine ((seminormKer (E := E) p).liftQ (evalL2ₗ (E := E) (H := H) T) hker).mkContinuous
      (C : ℝ) ?_
  intro x
  refine Quotient.inductionOn x ?_
  intro f
  change
      ‖(seminormKer (E := E) p).liftQ (evalL2ₗ (E := E) (H := H) T) hker
          (Submodule.Quotient.mk (p := seminormKer (E := E) p) f)‖
        ≤ (C : ℝ) *
            QuotBySeminorm.norm (E := E) p (Submodule.Quotient.mk (p := seminormKer (E := E) p) f)
  simpa [p, evalL2ₗ, evalL2, QuotBySeminorm.norm_mk, Submodule.liftQ_apply] using
    (norm_evalL2_le_of_le_seminormFamily (E := E) (H := H) (T := T) (n := n) (C := C) hle f)

/-- Extend the `L²` evaluation map to the local Banach space `BanachOfSeminorm (seminormFamily n)`. -/
noncomputable
def evalL2BanachCLM (T : E →ₗ[ℝ] H) (n : ℕ) (C : ℝ≥0)
    (hle : (normSeminorm ℝ H).comp T ≤ C • (seminormFamily (E := E) n)) :
    BanachOfSeminorm (E := E) (seminormFamily (E := E) n)
      →L[ℝ] (E → ℝ) →₂[gaussianProcess (E := E) (H := H) T] ℝ :=
  let e : QuotBySeminorm (E := E) (seminormFamily (E := E) n)
            →L[ℝ] BanachOfSeminorm (E := E) (seminormFamily (E := E) n) :=
      BanachOfSeminorm.coeCLM (E := E) (seminormFamily (E := E) n)
  let f0 :
      QuotBySeminorm (E := E) (seminormFamily (E := E) n)
        →L[ℝ] (E → ℝ) →₂[gaussianProcess (E := E) (H := H) T] ℝ :=
      evalL2QuotCLM (E := E) (H := H) T n C hle
  f0.extend e

@[simp]
lemma evalL2BanachCLM_coe (T : E →ₗ[ℝ] H) (n : ℕ) (C : ℝ≥0)
    (hle : (normSeminorm ℝ H).comp T ≤ C • (seminormFamily (E := E) n))
    (x : QuotBySeminorm (E := E) (seminormFamily (E := E) n)) :
    evalL2BanachCLM (E := E) (H := H) T n C hle
        (x : BanachOfSeminorm (E := E) (seminormFamily (E := E) n)) =
      evalL2QuotCLM (E := E) (H := H) T n C hle x := by
  simpa [evalL2BanachCLM] using
    (ContinuousLinearMap.extend_eq
      (f := evalL2QuotCLM (E := E) (H := H) T n C hle)
      (e := BanachOfSeminorm.coeCLM (E := E) (seminormFamily (E := E) n))
      (h_dense := BanachOfSeminorm.denseRange_coeCLM (E := E) (p := seminormFamily (E := E) n))
      (h_e := BanachOfSeminorm.isUniformInducing_coeCLM (E := E) (p := seminormFamily (E := E) n))
      x)

lemma evalL2BanachCLM_toBanach (T : E →ₗ[ℝ] H) (n : ℕ) (C : ℝ≥0)
    (hle : (normSeminorm ℝ H).comp T ≤ C • (seminormFamily (E := E) n)) (f : E) :
    evalL2BanachCLM (E := E) (H := H) T n C hle
        (toBanachOfSeminorm_seminormFamily (E := E) n f)
      = evalL2 (E := E) (H := H) T f := by
  -- Reduce to the quotient statement using `extend_eq` and evaluate the lift on representatives.
  let p : Seminorm ℝ E := seminormFamily (E := E) n
  have hcoe :
      toBanachOfSeminorm_seminormFamily (E := E) n f =
        ((Submodule.Quotient.mk (p := seminormKer (E := E) p) f : QuotBySeminorm (E := E) p) :
          BanachOfSeminorm (E := E) p) := by
    rfl
  simp [hcoe, evalL2BanachCLM_coe, evalL2QuotCLM, evalL2ₗ, evalL2, p, Submodule.liftQ_apply]

-- Restore the generic quotient-module topology instance for downstream modules.
attribute [instance] QuotientModule.Quotient.topologicalSpace

end MinlosGaussianSupport

end

end OSforGFF
