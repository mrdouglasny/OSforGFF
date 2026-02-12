import OSforGFF.MinlosGaussianKolmogorov
import OSforGFF.MinlosGaussianKolmogorovMoments
import OSforGFF.MinlosGaussianSeminormBoundsStd
import OSforGFF.NuclearSpaceStd
import Mathlib.Algebra.Module.RingHom
import Mathlib.LinearAlgebra.Countable
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Support/regularity lemmas for the Gaussian Kolmogorov construction

This file begins the hard “support on `WeakDual`” step of the Gaussian Minlos pipeline.

At this stage we focus on **countable** spans, where almost-sure linearity can be packaged without
running into uncountable intersections.
-/

open Complex MeasureTheory Filter
open scoped BigOperators ENNReal NNReal RealInnerProductSpace ProbabilityTheory

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
      simpa [hf0] using this
    exact le_antisymm hle0 (ProbabilityTheory.variance_nonneg (fun ω : E → ℝ => ω f) μ)
  have hEV0 : ProbabilityTheory.evariance (fun ω : E → ℝ => ω f) μ = 0 := by
    have : ENNReal.ofReal (Var[(fun ω : E → ℝ => ω f); μ]) =
        ProbabilityTheory.evariance (fun ω : E → ℝ => ω f) μ :=
      hmemLp.ofReal_variance_eq
    simpa [hvar0] using this.symm
  have h_ae_mean :
      (fun ω : E → ℝ => ω f) =ᵐ[μ] fun _ => μ[(fun ω : E → ℝ => ω f)] := by
    have hmeas : AEMeasurable (fun ω : E → ℝ => ω f) μ :=
      (measurable_pi_apply f).aemeasurable
    simpa using (ProbabilityTheory.evariance_eq_zero_iff (μ := μ) hmeas).1 hEV0
  have h_ae0 :
      (fun ω : E → ℝ => ω f) =ᵐ[μ] fun _ => (0 : ℝ) := by
    simpa [hmean] using h_ae_mean
  have : ∀ᵐ ω ∂μ, (ω f : ℝ) = 0 := by
    simpa [Filter.EventuallyEq] using h_ae0
  simpa [μ] using this

section QLinearKernel

variable {ι : Type*} [Countable ι] (v : ι → E)

-- Provide the canonical `ℚ`-module structure by restricting scalars along `ℚ →+* ℝ`.
local instance : Module ℚ E := Module.compHom E (algebraMap ℚ ℝ)

/-- The ℚ-submodule of `Submodule.span ℚ (Set.range v)` on which `seminormFamily n` vanishes. -/
def qSpanSeminormFamilyKer (n : ℕ) :
    Submodule ℚ (Submodule.span ℚ (Set.range v)) where
  carrier := {x | seminormFamily (E := E) n (x : E) = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    have hx0 : seminormFamily (E := E) n (x : E) = 0 := hx
    have hy0 : seminormFamily (E := E) n (y : E) = 0 := hy
    have hle :
        seminormFamily (E := E) n ((x + y : Submodule.span ℚ (Set.range v)) : E) ≤ 0 := by
      calc
        seminormFamily (E := E) n ((x + y : Submodule.span ℚ (Set.range v)) : E)
            ≤ seminormFamily (E := E) n (x : E) + seminormFamily (E := E) n (y : E) :=
          by simpa using (map_add_le_add (seminormFamily (E := E) n) (x : E) (y : E))
        _ = 0 := by simp [hx0, hy0]
    have hge : 0 ≤ seminormFamily (E := E) n ((x + y : Submodule.span ℚ (Set.range v)) : E) :=
      apply_nonneg _ _
    exact le_antisymm hle hge
  smul_mem' := by
    intro q x hx
    have hx0 : seminormFamily (E := E) n (x : E) = 0 := hx
    have :
        seminormFamily (E := E) n ((q • x : Submodule.span ℚ (Set.range v)) : E) =
          ‖(q : ℝ)‖ * seminormFamily (E := E) n (x : E) := by
      simpa using (map_smul_eq_mul (seminormFamily (E := E) n) (q : ℝ) (x : E))
    simpa [this, hx0]

omit [Countable ι] in
@[simp]
lemma mem_qSpanSeminormFamilyKer_iff (n : ℕ) (x : Submodule.span ℚ (Set.range v)) :
    x ∈ qSpanSeminormFamilyKer (E := E) (v := v) n ↔ seminormFamily (E := E) n (x : E) = 0 :=
  Iff.rfl

/-- On a countable ℚ-span, we can package *simultaneously*:

* existence of a ℚ-linear realization of the sample path, and
* vanishing on the kernel of a controlling seminorm from `NuclearSpaceStd`.

This is a preparatory step towards descending sample paths to local Banach quotients. -/
theorem ae_exists_qLinear_on_qSpan_and_vanish_seminormFamily_ker
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∃ L : Submodule.span ℚ (Set.range v) →ₗ[ℚ] ℝ,
          (∀ x : Submodule.span ℚ (Set.range v), L x = ω (x : E)) ∧
          (∀ x : Submodule.span ℚ (Set.range v),
            seminormFamily (E := E) n (x : E) = 0 → L x = 0)) := by
  rcases ae_eval_eq_zero_of_seminormFamily_eq_zero (E := E) (H := H) (T := T) h_sq with
    ⟨n, C, hC0, hker⟩
  refine ⟨n, C, hC0, ?_⟩
  have hLin :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∃ L : Submodule.span ℚ (Set.range v) →ₗ[ℚ] ℝ, ∀ x, L x = ω (x : E)) :=
    ae_exists_qLinear_on_qSpan (E := E) (H := H) (v := v) T
  have hKerAll :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∀ x : Submodule.span ℚ (Set.range v), seminormFamily (E := E) n (x : E) = 0 → ω (x : E) = 0) := by
    have hx :
        ∀ x : Submodule.span ℚ (Set.range v),
          ∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            seminormFamily (E := E) n (x : E) = 0 → ω (x : E) = 0 := by
      intro x
      simpa using (hker (x : E))
    refine (ae_all_iff).2 ?_
    intro x
    exact hx x
  filter_upwards [hLin, hKerAll] with ω hωLin hωKer
  rcases hωLin with ⟨L, hL⟩
  refine ⟨L, hL, ?_⟩
  intro x hx0
  simpa [hL x] using hωKer x hx0

/-- Strengthening of `ae_exists_qLinear_on_qSpan_and_vanish_seminormFamily_ker`:
the ℚ-linear realization factors through the quotient by the kernel submodule. -/
theorem ae_exists_qLinear_on_qSpan_quotient_seminormFamilyKer
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∃ Lq :
          (Submodule.span ℚ (Set.range v) ⧸ qSpanSeminormFamilyKer (E := E) (v := v) n) →ₗ[ℚ] ℝ,
          ∀ x : Submodule.span ℚ (Set.range v),
            Lq ((qSpanSeminormFamilyKer (E := E) (v := v) n).mkQ x) = ω (x : E)) := by
  rcases ae_exists_qLinear_on_qSpan_and_vanish_seminormFamily_ker (E := E) (H := H) (v := v) T h_sq with
    ⟨n, C, hC0, hpack⟩
  refine ⟨n, C, hC0, ?_⟩
  filter_upwards [hpack] with ω hω
  rcases hω with ⟨L, hL, hLker⟩
  let K : Submodule ℚ (Submodule.span ℚ (Set.range v)) :=
    qSpanSeminormFamilyKer (E := E) (v := v) n
  have hK : K ≤ LinearMap.ker L := by
    intro x hx
    have hx0 : seminormFamily (E := E) n (x : E) = 0 :=
      (mem_qSpanSeminormFamilyKer_iff (E := E) (v := v) n x).1 hx
    simpa [LinearMap.mem_ker] using hLker x hx0
  refine ⟨K.liftQ L hK, ?_⟩
  intro x
  simp [K, hL x]

end QLinearKernel

/-!
## Dense countable families in local Banach spaces

The local Banach spaces `BanachOfSeminorm (seminormFamily n)` will later be used to control
sample-path regularity. A first basic step is that the canonical map
`E → BanachOfSeminorm (seminormFamily n)` has dense range.

This lemma is intentionally stated without any continuity assumptions on `E → QuotBySeminorm p`,
avoiding clashes between the quotient topology inherited from `E` and the norm topology on
`QuotBySeminorm p`. -/

theorem denseRange_toBanachOfSeminorm_seminormFamily (n : ℕ) :
    DenseRange fun x : E =>
      (BanachOfSeminorm.coeCLM (E := E) (seminormFamily (E := E) n))
        (Submodule.Quotient.mk
          (p := seminormKer (E := E) (seminormFamily (E := E) n)) x) := by
  let p : Seminorm ℝ E := seminormFamily (E := E) n
  let f : E → QuotBySeminorm (E := E) p :=
    Submodule.Quotient.mk (p := seminormKer (E := E) p)
  let g : QuotBySeminorm (E := E) p → BanachOfSeminorm (E := E) p :=
    BanachOfSeminorm.coeCLM (E := E) p
  have hg : DenseRange g :=
    BanachOfSeminorm.denseRange_coeCLM (E := E) (p := p)
  have hf : Function.Surjective f :=
    Submodule.Quotient.mk_surjective (p := seminormKer (E := E) p)
  have hrange : Set.range (g ∘ f) = Set.range g := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨f x, rfl⟩
    · rintro ⟨xq, rfl⟩
      rcases hf xq with ⟨x, rfl⟩
      exact ⟨x, rfl⟩
  have hcomp : DenseRange (g ∘ f) := by
    simpa [DenseRange, hrange.symm] using hg
  simpa [p, f, g, Function.comp] using hcomp

section DenseCountableFamilies

open TopologicalSpace
open OSforGFF.NuclearSpaceStd

/-- For each local Banach space `BanachOfSeminorm (seminormFamily n)`, there exists a
countable family `v : ℕ → E` whose image is dense under the canonical map
`E → BanachOfSeminorm (seminormFamily n)`. -/
theorem exists_denseSeq_toBanachOfSeminorm_seminormFamily (n : ℕ) :
    ∃ v : ℕ → E, DenseRange fun k : ℕ =>
      (BanachOfSeminorm.coeCLM (E := E) (seminormFamily (E := E) n))
        (Submodule.Quotient.mk
          (p := seminormKer (E := E) (seminormFamily (E := E) n)) (v k)) := by
  let p : Seminorm ℝ E := seminormFamily (E := E) n
  let j : E → BanachOfSeminorm (E := E) p := fun x =>
    (BanachOfSeminorm.coeCLM (E := E) p)
      (Submodule.Quotient.mk (p := seminormKer (E := E) p) x)
  have hDense : DenseRange j := by
    simpa [j, p] using (denseRange_toBanachOfSeminorm_seminormFamily (E := E) (n := n))
  haveI : TopologicalSpace.SeparableSpace (BanachOfSeminorm (E := E) p) := by
    simpa [p] using (NuclearSpaceStd.separableSpace_banachOfSeminorm_seminormFamily (E := E) n)
  have hSep : TopologicalSpace.IsSeparable (Set.range j) :=
    TopologicalSpace.IsSeparable.of_separableSpace (s := Set.range j)
  rcases hSep.exists_countable_dense_subset with ⟨t, htj, htcount, hclosure⟩
  have ht_dense : Dense t := by
    have huniv : (Set.univ : Set (BanachOfSeminorm (E := E) p)) ⊆ closure t := by
      have : closure (Set.range j) ⊆ closure t := by
        simpa [closure_closure] using (closure_mono hclosure)
      simpa [hDense.closure_range] using this
    intro x
    exact huniv (by simp)
  have ht_nonempty : t.Nonempty := by
    have h_range_nonempty : (Set.range j).Nonempty := ⟨j 0, ⟨0, rfl⟩⟩
    have ht_ne : t ≠ (∅ : Set (BanachOfSeminorm (E := E) p)) := by
      intro ht0
      have : Set.range j ⊆ (∅ : Set (BanachOfSeminorm (E := E) p)) := by
        simp [ht0] at hclosure
      have : Set.range j = (∅ : Set (BanachOfSeminorm (E := E) p)) :=
        (Set.subset_empty_iff).1 this
      exact h_range_nonempty.ne_empty this
    exact Set.nonempty_iff_ne_empty.2 ht_ne
  rcases htcount.exists_eq_range ht_nonempty with ⟨u, rfl⟩
  have hu_in : ∀ k : ℕ, u k ∈ Set.range j := by
    intro k
    exact htj (Set.mem_range_self k)
  choose v hv using hu_in
  refine ⟨v, ?_⟩
  have : (fun k : ℕ => j (v k)) = u := by
    funext k
    simpa using (hv k)
  have hu_dense : DenseRange u := by
    simpa [DenseRange] using ht_dense
  simpa [this, j, p] using hu_dense

/-- A single countable family dense in *all* local Banach spaces
`BanachOfSeminorm (seminormFamily n)`. -/
theorem exists_denseSeq_family_toBanachOfSeminorm_seminormFamily :
    ∃ v : (ℕ × ℕ) → E,
      ∀ n : ℕ, DenseRange fun k : ℕ =>
        (BanachOfSeminorm.coeCLM (E := E) (seminormFamily (E := E) n))
          (Submodule.Quotient.mk
            (p := seminormKer (E := E) (seminormFamily (E := E) n)) (v (n, k))) := by
  choose v hv using fun n : ℕ =>
    exists_denseSeq_toBanachOfSeminorm_seminormFamily (E := E) (n := n)
  refine ⟨fun nk => v nk.1 nk.2, ?_⟩
  intro n
  simpa using hv n

end DenseCountableFamilies

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
  have hcheb :
      μ {ω | c ≤ |(ω f : ℝ) - μ[(fun ω : E → ℝ => ω f)]|} ≤
        ENNReal.ofReal (Var[(fun ω : E → ℝ => ω f); μ] / c ^ 2) := by
    simpa [μ] using (ProbabilityTheory.meas_ge_le_variance_div_sq (μ := μ) hMemLp hc)
  have hevent :
      {ω : E → ℝ | c ≤ |(ω f : ℝ) - μ[(fun ω : E → ℝ => ω f)]|} =
        {ω : E → ℝ | c ≤ |(ω f : ℝ)|} := by
    ext ω
    simp [hmean]
  have hvar_le' :
      Var[(fun ω : E → ℝ => ω f); μ] ≤ ((C : ℝ) * (seminormFamily (E := E) n) f) ^ 2 := by
    simpa [μ] using hvar_le f
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

set_option maxHeartbeats 400000 in
/-- **Borel–Cantelli consequence of the Chebyshev bound.**

For the controlling seminorm `seminormFamily n`, if a sequence `(u k)` has square-summable
seminorm values, then evaluations `ω (u k)` converge to `0` almost surely. -/
theorem exists_ae_tendsto_eval_atTop_nhds_zero_of_summable_seminormFamily_sq
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ u : ℕ → E,
        Summable (fun k : ℕ => (seminormFamily (E := E) n (u k)) ^ 2) →
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            Tendsto (fun k : ℕ => (ω (u k) : ℝ)) atTop (nhds 0)) := by
  rcases exists_prob_abs_eval_ge_le_seminormFamily (E := E) (H := H) (T := T) h_sq with
    ⟨n, C, hC0, hprob⟩
  refine ⟨n, C, hC0, ?_⟩
  intro u hsum
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  have hAE_eps :
      ∀ m : ℕ,
        (∀ᵐ ω ∂μ, ∀ᶠ k in atTop, |(ω (u k) : ℝ)| < (1 / (m + 1 : ℝ))) := by
    intro m
    -- we apply Borel–Cantelli to the sets `{ω | ε ≤ |ω(u k)|}` with `ε = 1/(m+1)`.
    have hε : 0 < (1 / (m + 1 : ℝ)) := by positivity
    let s : ℕ → Set (E → ℝ) := fun k => {ω | (1 / (m + 1 : ℝ)) ≤ |(ω (u k) : ℝ)|}
    have hs_le :
        ∀ k : ℕ, μ (s k) ≤
          ENNReal.ofReal ((((C : ℝ) * (seminormFamily (E := E) n (u k))) ^ 2) /
            ((1 / (m + 1 : ℝ)) ^ 2)) := by
      intro k
      simpa [μ, s] using (hprob (u k) (c := (1 / (m + 1 : ℝ))) hε)
    have hsum_real :
        Summable (fun k : ℕ =>
          ((((C : ℝ) * (seminormFamily (E := E) n (u k))) ^ 2) /
            ((1 / (m + 1 : ℝ)) ^ 2))) := by
      have hsumCp :
          Summable (fun k : ℕ =>
            (((C : ℝ) * (seminormFamily (E := E) n (u k))) ^ 2)) := by
        have hscaled :
            Summable (fun k : ℕ =>
              ((C : ℝ) ^ 2) * ((seminormFamily (E := E) n (u k)) ^ 2)) :=
          hsum.mul_left ((C : ℝ) ^ 2)
        refine hscaled.congr (fun k => ?_)
        simp [mul_pow]
      have hsumMul :
          Summable (fun k : ℕ =>
            (((C : ℝ) * (seminormFamily (E := E) n (u k))) ^ 2) * ((m + 1 : ℝ) ^ 2)) := by
        have h := hsumCp.mul_left ((m + 1 : ℝ) ^ 2)
        refine h.congr (fun k => ?_)
        simp [mul_comm]
      refine hsumMul.congr (fun k => ?_)
      field_simp
    have hsum_ennreal :
        (∑' k : ℕ,
            ENNReal.ofReal
              ((((C : ℝ) * (seminormFamily (E := E) n (u k))) ^ 2) /
                ((1 / (m + 1 : ℝ)) ^ 2))) ≠ ∞ :=
      hsum_real.tsum_ofReal_ne_top
    have hs_tsum_ne_top : (∑' k : ℕ, μ (s k)) ≠ ∞ := by
      have hle_tsum :
          (∑' k : ℕ, μ (s k)) ≤
            ∑' k : ℕ,
              ENNReal.ofReal
                ((((C : ℝ) * (seminormFamily (E := E) n (u k))) ^ 2) /
                  ((1 / (m + 1 : ℝ)) ^ 2)) :=
        ENNReal.tsum_le_tsum (fun k => hs_le k)
      exact ne_top_of_le_ne_top hsum_ennreal hle_tsum
    have hAE := (MeasureTheory.ae_eventually_notMem (μ := μ) (s := s) hs_tsum_ne_top)
    filter_upwards [hAE] with ω hω
    have : ∀ᶠ k in atTop, ¬((1 / (m + 1 : ℝ)) ≤ |(ω (u k) : ℝ)|) := by
      simpa [s] using hω
    filter_upwards [this] with k hk
    exact lt_of_not_ge hk
  have hAE_all :
      (∀ᵐ ω ∂μ,
        ∀ m : ℕ, ∀ᶠ k in atTop, |(ω (u k) : ℝ)| < (1 / (m + 1 : ℝ))) := by
    exact (MeasureTheory.ae_all_iff).2 hAE_eps
  filter_upwards [hAE_all] with ω hω
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  have h_event : ∀ᶠ k in atTop, |(ω (u k) : ℝ)| < (1 / (m + 1 : ℝ)) := hω m
  have h_event' : ∀ᶠ k in atTop, |(ω (u k) : ℝ)| < ε :=
    h_event.mono (fun k hk => lt_trans hk hm)
  simpa [Real.dist_0_eq_abs] using h_event'

/-- **Borel–Cantelli with varying thresholds** (seminorm-controlled Gaussian process).

If a sequence `(u k)` has small seminorm values compared to a threshold sequence `(c k)` in a
square-summable way, then almost surely `|ω (u k)| < c k` eventually. -/
theorem exists_ae_eventually_abs_eval_lt_of_summable_seminormFamily_sq_div
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ u : ℕ → E, ∀ c : ℕ → ℝ,
        (∀ k, 0 < c k) →
        Summable (fun k : ℕ =>
          ((((C : ℝ) * (seminormFamily (E := E) n (u k))) ^ 2) / ((c k) ^ 2))) →
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            ∀ᶠ k in atTop, |(ω (u k) : ℝ)| < c k) := by
  rcases exists_prob_abs_eval_ge_le_seminormFamily (E := E) (H := H) (T := T) h_sq with
    ⟨n, C, hC0, hprob⟩
  refine ⟨n, C, hC0, ?_⟩
  intro u c hc hsum
  let μ : Measure (E → ℝ) := gaussianProcess (E := E) (H := H) T
  let s : ℕ → Set (E → ℝ) := fun k => {ω | c k ≤ |(ω (u k) : ℝ)|}
  have hs_le :
      ∀ k : ℕ, μ (s k) ≤
        ENNReal.ofReal
          ((((C : ℝ) * (seminormFamily (E := E) n (u k))) ^ 2) / ((c k) ^ 2)) := by
    intro k
    simpa [μ, s] using (hprob (u k) (c := c k) (hc k))
  have hsum_ennreal :
      (∑' k : ℕ,
          ENNReal.ofReal
            ((((C : ℝ) * (seminormFamily (E := E) n (u k))) ^ 2) / ((c k) ^ 2))) ≠ ∞ :=
    hsum.tsum_ofReal_ne_top
  have hs_tsum_ne_top : (∑' k : ℕ, μ (s k)) ≠ ∞ := by
    have hle_tsum :
        (∑' k : ℕ, μ (s k)) ≤
          ∑' k : ℕ,
            ENNReal.ofReal
              ((((C : ℝ) * (seminormFamily (E := E) n (u k))) ^ 2) / ((c k) ^ 2)) :=
      ENNReal.tsum_le_tsum (fun k => hs_le k)
    exact ne_top_of_le_ne_top hsum_ennreal hle_tsum
  have hAE := (MeasureTheory.ae_eventually_notMem (μ := μ) (s := s) hs_tsum_ne_top)
  filter_upwards [hAE] with ω hω
  have : ∀ᶠ k in atTop, ¬(c k ≤ |(ω (u k) : ℝ)|) := by
    simpa [s] using hω
  filter_upwards [this] with k hk
  exact lt_of_not_ge hk

/-- **Absolute summability criterion** (via Borel–Cantelli and a comparison series).

If eventually `|ω (u k)|` is bounded by a summable deterministic majorant `c k`, then the series
`∑ |ω (u k)|` converges almost surely.  We obtain this under the same seminorm-squared summability
assumption as in `exists_ae_eventually_abs_eval_lt_of_summable_seminormFamily_sq_div`. -/
theorem exists_ae_summable_abs_eval_of_summable_seminormFamily_sq_div
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ u : ℕ → E, ∀ c : ℕ → ℝ,
        (∀ k, 0 < c k) →
        Summable c →
        Summable (fun k : ℕ =>
          ((((C : ℝ) * (seminormFamily (E := E) n (u k))) ^ 2) / ((c k) ^ 2))) →
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            Summable (fun k : ℕ => |(ω (u k) : ℝ)|)) := by
  rcases exists_ae_eventually_abs_eval_lt_of_summable_seminormFamily_sq_div
      (E := E) (H := H) (T := T) h_sq with ⟨n, C, hC0, hAE⟩
  refine ⟨n, C, hC0, ?_⟩
  intro u c hc hsumc hsum
  have h_event :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∀ᶠ k in atTop, |(ω (u k) : ℝ)| < c k) :=
    hAE u c hc hsum
  filter_upwards [h_event] with ω hω
  rcases (eventually_atTop.1 hω) with ⟨N, hN⟩
  have htail :
      Summable (fun k : ℕ => |(ω (u (k + N)) : ℝ)|) := by
    have hle : ∀ k : ℕ, |(ω (u (k + N)) : ℝ)| ≤ c (k + N) := by
      intro k
      exact le_of_lt (hN (k + N) (Nat.le_add_left _ _))
    have hsum_tail_c : Summable (fun k : ℕ => c (k + N)) :=
      (_root_.summable_nat_add_iff N).2 hsumc
    exact Summable.of_nonneg_of_le (fun k => abs_nonneg _) hle hsum_tail_c
  exact (_root_.summable_nat_add_iff N).1 htail

/-- **Cauchy criterion for evaluations along fast Cauchy sequences in `E`.**

If increments `w (k+1) - w k` are small enough in the controlling seminorm (at a polynomial rate),
then almost surely `k ↦ ω (w k)` is a Cauchy sequence. This is a convenient input for defining
limits along completions of seminorm quotients. -/
theorem exists_ae_cauchySeq_eval_of_le_pow_four
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ w : ℕ → E,
        (∀ k : ℕ, seminormFamily (E := E) n (w (k + 1) - w k) ≤ (1 / ((k + 1 : ℕ) : ℝ) ^ 4)) →
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            CauchySeq (fun k : ℕ => (ω (w k) : ℝ))) := by
  rcases exists_ae_summable_abs_eval_of_summable_seminormFamily_sq_div
      (E := E) (H := H) (T := T) h_sq with ⟨n, C, hC0, hsumAE⟩
  refine ⟨n, C, hC0, ?_⟩
  intro w hw
  let u : ℕ → E := fun k => w (k + 1) - w k
  let c : ℕ → ℝ := fun k => 1 / ((k + 1 : ℕ) : ℝ) ^ 2
  have hc_pos : ∀ k : ℕ, 0 < c k := by
    intro k
    have : 0 < ((k + 1 : ℕ) : ℝ) ^ 2 := by positivity
    simpa [c] using (one_div_pos.2 this)
  have hsum_c : Summable c := by
    have h0 : Summable (fun n : ℕ => (1 / ((n : ℝ) ^ (2 : ℕ)) : ℝ)) :=
      (Real.summable_one_div_nat_pow (p := 2)).2 (by decide)
    simpa [c] using ((_root_.summable_nat_add_iff 1).2 h0)
  have hsum_ratio :
      Summable (fun k : ℕ =>
        ((((C : ℝ) * seminormFamily (E := E) n (u k)) ^ 2) / ((c k) ^ 2))) := by
    have hle :
        ∀ k : ℕ,
          ((((C : ℝ) * seminormFamily (E := E) n (u k)) ^ 2) / ((c k) ^ 2))
            ≤ ((C : ℝ) ^ 2) * (1 / ((k + 1 : ℕ) : ℝ) ^ 4) := by
      intro k
      have hp : seminormFamily (E := E) n (u k) ≤ 1 / ((k + 1 : ℕ) : ℝ) ^ 4 := by
        simpa [u] using hw k
      have hp_nonneg : 0 ≤ seminormFamily (E := E) n (u k) := apply_nonneg _ _
      have hC_nonneg : 0 ≤ (C : ℝ) := by exact_mod_cast C.2
      have hc_sq : (c k) ^ 2 = 1 / ((k + 1 : ℕ) : ℝ) ^ 4 := by
        have hpow : ((↑k + 1 : ℝ) ^ 2) ^ 2 = (↑k + 1 : ℝ) ^ 4 := by
          simpa using (pow_mul (↑k + 1 : ℝ) 2 2).symm
        simp [c, Nat.cast_add, hpow]
      have hsq :
          ((seminormFamily (E := E) n (u k)) ^ 2) ≤ (1 / ((k + 1 : ℕ) : ℝ) ^ 4) ^ 2 :=
        pow_le_pow_left₀ hp_nonneg hp 2
      calc
        ((((C : ℝ) * seminormFamily (E := E) n (u k)) ^ 2) / ((c k) ^ 2))
            = (((C : ℝ) ^ 2) * ((seminormFamily (E := E) n (u k)) ^ 2)) / ((c k) ^ 2) := by
                simp [mul_pow]
        _ ≤ (((C : ℝ) ^ 2) * ((1 / ((k + 1 : ℕ) : ℝ) ^ 4) ^ 2)) / ((c k) ^ 2) := by
              gcongr
        _ = ((C : ℝ) ^ 2) * (1 / ((k + 1 : ℕ) : ℝ) ^ 4) := by
              have ha0 : (1 / ((k + 1 : ℕ) : ℝ) ^ 4 : ℝ) ≠ 0 := by
                have hk0 : (((k + 1 : ℕ) : ℝ) ^ 4 : ℝ) ≠ 0 := by
                  exact pow_ne_zero 4 (by exact_mod_cast (Nat.succ_ne_zero k))
                exact one_div_ne_zero hk0
              rw [hc_sq]
              have :
                  ((1 / ((k + 1 : ℕ) : ℝ) ^ 4) ^ 2) / (1 / ((k + 1 : ℕ) : ℝ) ^ 4)
                    = (1 / ((k + 1 : ℕ) : ℝ) ^ 4) := by
                have h :=
                  (mul_div_cancel_right₀ (1 / ((k + 1 : ℕ) : ℝ) ^ 4)
                    (b := 1 / ((k + 1 : ℕ) : ℝ) ^ 4) ha0)
                simpa only [pow_two] using h
              rw [mul_div_assoc]
              exact congrArg (fun t : ℝ => ((C : ℝ) ^ 2) * t) this
    have hnonneg :
        ∀ k : ℕ, 0 ≤
          ((((C : ℝ) * seminormFamily (E := E) n (u k)) ^ 2) / ((c k) ^ 2)) := by
      intro k
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hsum_base : Summable (fun k : ℕ => ((C : ℝ) ^ 2) * (1 / ((k + 1 : ℕ) : ℝ) ^ 4)) := by
      have h0 : Summable (fun n : ℕ => (1 / ((n : ℝ) ^ (4 : ℕ)) : ℝ)) :=
        (Real.summable_one_div_nat_pow (p := 4)).2 (by decide)
      have h0' : Summable (fun k : ℕ => (1 / ((k + 1 : ℕ) : ℝ) ^ 4 : ℝ)) := by
        simpa using ((_root_.summable_nat_add_iff 1).2 h0)
      exact h0'.mul_left ((C : ℝ) ^ 2)
    exact Summable.of_nonneg_of_le hnonneg hle hsum_base
  have hsum_abs :
      ∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        Summable (fun k : ℕ => |(ω (u k) : ℝ)|) :=
    hsumAE (u := u) (c := c) hc_pos hsum_c hsum_ratio
  let v : (ℕ ⊕ ℕ) → E := fun s =>
    Sum.rec (fun k => w k) (fun k => u k) s
  have hadd :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∀ i j : (ℕ ⊕ ℕ), ω (v i + v j) = ω (v i) + ω (v j)) := by
    simpa [v] using (OSforGFF.MinlosGaussianKolmogorov.ae_eval_add_all
      (E := E) (H := H) (T := T) v)
  filter_upwards [hsum_abs, hadd] with ω hsumω haddω
  have hdist :
      Summable (fun k : ℕ => dist (ω (w k) : ℝ) (ω (w (k + 1)) : ℝ)) := by
    have hdiff :
        ∀ k : ℕ, dist (ω (w k) : ℝ) (ω (w (k + 1)) : ℝ) = |(ω (u k) : ℝ)| := by
      intro k
      have haddk :
          ω (w k + u k) = ω (w k) + ω (u k) := by
        simpa [v] using haddω (Sum.inl k) (Sum.inr k)
      have hwku : w k + u k = w (k + 1) := by
        simp [u, add_comm, sub_eq_add_neg]
      have hlin : (ω (w (k + 1)) : ℝ) = ω (w k) + ω (u k) := by
        simpa [hwku] using haddk
      have hsub : (ω (w (k + 1)) : ℝ) - ω (w k) = ω (u k) := by
        simp [hlin]
      have habs :
          |(ω (w (k + 1)) : ℝ) - ω (w k)| = |(ω (u k) : ℝ)| := by
        simpa using congrArg abs hsub
      simpa [Real.dist_eq, abs_sub_comm] using habs
    simpa [hdiff] using hsumω
  exact cauchySeq_of_summable_dist (f := fun k : ℕ => (ω (w k) : ℝ)) hdist

end VarianceBounds

end MinlosGaussianSupport

end

end OSforGFF
