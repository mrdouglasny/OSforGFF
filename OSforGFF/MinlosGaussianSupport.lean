import OSforGFF.MinlosGaussianKolmogorov
import OSforGFF.MinlosGaussianKolmogorovMoments
import OSforGFF.MinlosGaussianSeminormBoundsStd
import OSforGFF.NuclearSpaceStd
import Mathlib.Algebra.Module.RingHom
import Mathlib.LinearAlgebra.Countable

/-!
# Support/regularity lemmas for the Gaussian Kolmogorov construction

This file begins the hard “support on `WeakDual`” step of the Gaussian Minlos pipeline.

At this stage we focus on **countable** spans, where almost-sure linearity can be packaged without
running into uncountable intersections.
-/

open Complex MeasureTheory
open scoped BigOperators NNReal RealInnerProductSpace ProbabilityTheory

namespace OSforGFF

noncomputable section

namespace MinlosGaussianSupport

open OSforGFF.MinlosGaussianKolmogorov

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-!
## Almost-sure ℚ-linearity on a countable span

We package the “simultaneous” additivity and ℚ-homogeneity lemmas from
`OSforGFF.MinlosGaussianKolmogorov` into an existence statement of a ℚ-linear map on the
ℚ-submodule spanned by a countable family.
-/

section QLinearOnSpan

variable {ι : Type*} [Countable ι] (v : ι → E)

-- Provide the canonical `ℚ`-module structure by restricting scalars along `ℚ →+* ℝ`.
local instance : Module ℚ E := Module.compHom E (algebraMap ℚ ℝ)

omit [TopologicalSpace E] in
/-- Almost surely, a sample `ω : E → ℝ` restricts to a ℚ-linear map on the ℚ-span of a
countable family `v`. -/
theorem ae_exists_qLinear_on_qSpan (T : E →ₗ[ℝ] H) :
    (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
      ∃ L : Submodule.span ℚ (Set.range v) →ₗ[ℚ] ℝ, ∀ x, L x = ω (x : E)) := by
  let v' : Submodule.span ℚ (Set.range v) → E := fun x => (x : E)
  have hadd :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∀ x y : Submodule.span ℚ (Set.range v),
          ω (v' x + v' y) = ω (v' x) + ω (v' y)) := by
    simpa [v'] using (ae_eval_add_all (E := E) (H := H) (T := T) v')
  have hsmul :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∀ q : ℚ, ∀ x : Submodule.span ℚ (Set.range v),
          ω ((q : ℝ) • v' x) = (q : ℝ) • (ω (v' x))) := by
    simpa [v'] using (ae_eval_smul_all_rat (E := E) (H := H) (T := T) v')
  filter_upwards [hadd, hsmul] with ω hω_add hω_smul
  refine ⟨
    { toFun := fun x => ω (x : E)
      map_add' := ?_
      map_smul' := ?_ }, ?_⟩
  · intro x y
    simpa [v'] using (hω_add x y)
  · intro q x
    simpa [v'] using (hω_smul q x)
  · intro x
    rfl

end QLinearOnSpan

/-!
## Variance bounds from seminorm control

For later continuity/tightness arguments we record the basic bound on variances that comes from
controlling `‖T ·‖` by one of the seminorms in the chosen `NuclearSpaceStd` family.
-/

section VarianceBounds

open OSforGFF.NuclearSpaceStd
open OSforGFF.MinlosGaussianSeminormBoundsStd

variable [NuclearSpaceStd E]

/-- If `‖T ·‖²` is continuous, then the evaluation variance is controlled by one of the
`NuclearSpaceStd` seminorms. -/
theorem exists_variance_le_seminormFamily
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ f : E,
        Var[(fun ω : E → ℝ => ω f); gaussianProcess (E := E) (H := H) T] ≤
          ((C : ℝ) * (seminormFamily (E := E) n) f) ^ 2 := by
  rcases exists_bound_seminormFamily (E := E) (H := H) T h_sq with ⟨n, C, hC0, hle⟩
  refine ⟨n, C, hC0, ?_⟩
  intro f
  have hvar :
      Var[(fun ω : E → ℝ => ω f); gaussianProcess (E := E) (H := H) T] = (‖T f‖ ^ 2 : ℝ) := by
    simpa using (variance_eval_eq (E := E) (H := H) (T := T) f)
  have hTf : ‖T f‖ ≤ (C : ℝ) * (seminormFamily (E := E) n) f := by
    have := hle f
    simpa [Seminorm.comp_apply, Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc] using this
  have hTf_sq :
      (‖T f‖ ^ 2 : ℝ) ≤ ((C : ℝ) * (seminormFamily (E := E) n) f) ^ 2 := by
    have hnonneg : (0 : ℝ) ≤ (C : ℝ) * (seminormFamily (E := E) n) f := by
      have : (0 : ℝ) ≤ (C : ℝ) := by exact_mod_cast C.2
      exact mul_nonneg this (apply_nonneg _ _)
    simpa [pow_two] using (mul_le_mul hTf hTf (norm_nonneg _) hnonneg)
  simpa [hvar] using hTf_sq

/-- If `f` is in the kernel of the controlling seminorm, then `ω f = 0` almost surely. -/
theorem ae_eval_eq_zero_of_seminormFamily_eq_zero
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ f : E, seminormFamily (E := E) n f = 0 →
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T), (ω f : ℝ) = 0) := by
  rcases exists_variance_le_seminormFamily (E := E) (H := H) T h_sq with ⟨n, C, hC0, hvar_le⟩
  refine ⟨n, C, hC0, ?_⟩
  intro f hf0
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  have hmemLp : MeasureTheory.MemLp (fun ω : E → ℝ => ω f) 2 μ := by
    simpa [μ] using (memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp))
  have hmean : μ[(fun ω : E → ℝ => ω f)] = 0 := by
    simpa [μ] using (integral_eval_eq_zero (E := E) (H := H) (T := T) f)
  have hvar0 : Var[(fun ω : E → ℝ => ω f); μ] = 0 := by
    have hle0 :
        Var[(fun ω : E → ℝ => ω f); μ] ≤ 0 := by
      have : Var[(fun ω : E → ℝ => ω f); μ] ≤ ((C : ℝ) * (seminormFamily (E := E) n) f) ^ 2 :=
        by simpa [μ] using hvar_le f
      -- the RHS is `0` because `seminormFamily n f = 0`
      simpa [hf0] using this
    exact le_antisymm hle0 (ProbabilityTheory.variance_nonneg (fun ω : E → ℝ => ω f) μ)
  -- Convert `Var = 0` to `ae`-equality with the mean.
  have hEV0 : ProbabilityTheory.evariance (fun ω : E → ℝ => ω f) μ = 0 := by
    -- `eVar = ofReal Var` under `MemLp`.
    have : ENNReal.ofReal (Var[(fun ω : E → ℝ => ω f); μ]) =
        ProbabilityTheory.evariance (fun ω : E → ℝ => ω f) μ :=
      hmemLp.ofReal_variance_eq
    simpa [hvar0] using this.symm
  have h_ae_mean :
      (fun ω : E → ℝ => ω f) =ᵐ[μ] fun _ => μ[(fun ω : E → ℝ => ω f)] := by
    have hmeas : AEMeasurable (fun ω : E → ℝ => ω f) μ :=
      (measurable_pi_apply f).aemeasurable
    simpa using (ProbabilityTheory.evariance_eq_zero_iff (μ := μ) hmeas).1 hEV0
  -- Finish by rewriting the mean as `0`.
  have h_ae0 :
      (fun ω : E → ℝ => ω f) =ᵐ[μ] fun _ => (0 : ℝ) := by
    simpa [hmean] using h_ae_mean
  -- Unpack the `ae` statement.
  have : ∀ᵐ ω ∂μ, (ω f : ℝ) = 0 := by
    simpa [Filter.EventuallyEq] using h_ae0
  simpa [μ] using this

/-- Chebyshev bound for the evaluation random variables, using the seminorm control coming from
`NuclearSpaceStd`. -/
theorem exists_prob_abs_eval_ge_le_seminormFamily
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ f : E, ∀ {c : ℝ}, 0 < c →
        (gaussianProcess (E := E) (H := H) T) {ω | c ≤ |(ω f : ℝ)|} ≤
          ENNReal.ofReal ((((C : ℝ) * (seminormFamily (E := E) n) f) ^ 2) / (c ^ 2)) := by
  rcases exists_variance_le_seminormFamily (E := E) (H := H) T h_sq with ⟨n, C, hC0, hvar_le⟩
  refine ⟨n, C, hC0, ?_⟩
  intro f c hc
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  have hMemLp : MemLp (fun ω : E → ℝ => ω f) 2 μ := by
    simpa [μ] using (memLp_eval (E := E) (H := H) (T := T) f (p := (2 : ENNReal)) (by simp))
  have hmean : μ[(fun ω : E → ℝ => ω f)] = 0 := by
    simpa [μ] using (integral_eval_eq_zero (E := E) (H := H) (T := T) f)
  -- Apply Chebyshev to `X = fun ω => ω f`, and rewrite `μ[X] = 0`.
  have hcheb :
      μ {ω | c ≤ |(ω f : ℝ) - μ[(fun ω : E → ℝ => ω f)]|} ≤
        ENNReal.ofReal (Var[(fun ω : E → ℝ => ω f); μ] / c ^ 2) := by
    simpa [μ] using (ProbabilityTheory.meas_ge_le_variance_div_sq (μ := μ) hMemLp hc)
  -- Rewrite the event and use the variance bound.
  have hevent :
      {ω : E → ℝ | c ≤ |(ω f : ℝ) - μ[(fun ω : E → ℝ => ω f)]|} =
        {ω : E → ℝ | c ≤ |(ω f : ℝ)|} := by
    ext ω
    simp [hmean]
  have hvar_le' :
      Var[(fun ω : E → ℝ => ω f); μ] ≤ ((C : ℝ) * (seminormFamily (E := E) n) f) ^ 2 := by
    simpa [μ] using hvar_le f
  -- Combine.
  have hdiv :
      Var[(fun ω : E → ℝ => ω f); μ] / c ^ 2 ≤
        (((C : ℝ) * (seminormFamily (E := E) n) f) ^ 2) / c ^ 2 := by
    exact div_le_div_of_nonneg_right hvar_le' (sq_nonneg c)
  have hof :
      ENNReal.ofReal (Var[(fun ω : E → ℝ => ω f); μ] / c ^ 2) ≤
        ENNReal.ofReal ((((C : ℝ) * (seminormFamily (E := E) n) f) ^ 2) / c ^ 2) :=
    ENNReal.ofReal_le_ofReal hdiv
  have := hcheb.trans hof
  simpa [μ, hevent] using this

end VarianceBounds

end MinlosGaussianSupport

end

end OSforGFF
