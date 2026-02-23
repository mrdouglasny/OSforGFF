/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.MinlosGaussianSupport
import BrownianMotion.Continuity.KolmogorovChentsov

/-!
# Measurable `limUnder` extensions for the Gaussian Minlos support step

This file packages a small but important technical ingredient: **measurability** of the
`limUnder`-based limits that arise when we define sample-path extensions on local Banach
completions.

We reuse the general measurability lemmas for `limUnder` from the `BrownianMotion` development.
-/

open MeasureTheory Filter

open scoped NNReal

namespace OSforGFF

noncomputable section

namespace MinlosGaussianSupport

open OSforGFF.NuclearSpaceStd

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

section FastApproxChoice

variable [NuclearSpaceStd E]

/-- A (noncomputable) choice of a fast approximation sequence in the local Banach space
`BanachOfSeminorm (seminormFamily n)`. -/
noncomputable
def fastApproxSeq (n : ℕ) (v : ℕ → E)
    (hv : DenseRange fun k : ℕ =>
      toBanachOfSeminorm_seminormFamily (E := E) n (v k))
    (x : BanachOfSeminorm (E := E) (seminormFamily (E := E) n)) : ℕ → E :=
  Classical.choose
    (exists_fastCauchySeq_toBanachOfSeminorm_seminormFamily (E := E) (n := n) (v := v) hv x)

lemma fastApproxSeq_spec (n : ℕ) (v : ℕ → E)
    (hv : DenseRange fun k : ℕ =>
      toBanachOfSeminorm_seminormFamily (E := E) n (v k))
    (x : BanachOfSeminorm (E := E) (seminormFamily (E := E) n)) :
    (∀ k : ℕ,
        dist x (toBanachOfSeminorm_seminormFamily (E := E) n (fastApproxSeq (E := E) n v hv x k))
          < (1 / (2 * ((k + 1 : ℕ) : ℝ) ^ 4))) ∧
      (∀ k : ℕ,
        seminormFamily (E := E) n
            (fastApproxSeq (E := E) n v hv x (k + 1) - fastApproxSeq (E := E) n v hv x k)
          ≤ (1 / ((k + 1 : ℕ) : ℝ) ^ 4)) :=
  Classical.choose_spec
    (exists_fastCauchySeq_toBanachOfSeminorm_seminormFamily (E := E) (n := n) (v := v) hv x)

end FastApproxChoice

section LimUnderMeasurability

variable [NuclearSpaceStd E]

open scoped Topology

/-- For fixed `x` in the local Banach space, the `limUnder` of evaluations along a chosen fast
approximation sequence is a **measurable** function of the sample `ω : E → ℝ`. -/
theorem measurable_limUnder_eval_fastApproxSeq
    (n : ℕ) (v : ℕ → E)
    (hv : DenseRange fun k : ℕ =>
      toBanachOfSeminorm_seminormFamily (E := E) n (v k))
    (x : BanachOfSeminorm (E := E) (seminormFamily (E := E) n)) :
    Measurable fun ω : (E → ℝ) =>
      limUnder atTop (fun k : ℕ => (ω (fastApproxSeq (E := E) n v hv x k) : ℝ)) := by
  -- This is exactly `BrownianMotion`'s measurable `limUnder` lemma, specialized to `ι = ℕ`.
  refine measurable_limUnder (ι := ℕ) (X := (E → ℝ)) (E := ℝ)
    (l := (atTop : Filter ℕ))
    (f := fun k (ω : E → ℝ) => (ω (fastApproxSeq (E := E) n v hv x k) : ℝ)) ?_
  intro k
  simpa using (measurable_pi_apply (fastApproxSeq (E := E) n v hv x k))

end LimUnderMeasurability

section AETendstoLimUnder

open OSforGFF.MinlosGaussianKolmogorov

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NuclearSpaceStd E]

/-- If we choose a fast approximation sequence for `x` (deterministically, by choice), then along
that sequence the evaluations `ω ↦ ω (w k)` converge almost surely. In particular they converge to
the `limUnder` of the sequence. -/
theorem exists_ae_tendsto_limUnder_eval_fastApproxSeq
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ (v : ℕ → E)
        (hv : DenseRange fun k : ℕ =>
          toBanachOfSeminorm_seminormFamily (E := E) n (v k))
        (x : BanachOfSeminorm (E := E) (seminormFamily (E := E) n)),
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            Tendsto
              (fun k : ℕ => (ω (fastApproxSeq (E := E) n v hv x k) : ℝ)) atTop
              (nhds (limUnder atTop fun k : ℕ => (ω (fastApproxSeq (E := E) n v hv x k) : ℝ)))) := by
  rcases exists_ae_tendsto_eval_of_le_pow_four (E := E) (H := H) (T := T) h_sq with ⟨n, C, hC0, hAE⟩
  refine ⟨n, C, hC0, ?_⟩
  intro v hv x
  have hinc :
      ∀ k : ℕ,
        seminormFamily (E := E) n
            (fastApproxSeq (E := E) n v hv x (k + 1) - fastApproxSeq (E := E) n v hv x k)
          ≤ (1 / ((k + 1 : ℕ) : ℝ) ^ 4) :=
    (fastApproxSeq_spec (E := E) (n := n) (v := v) hv x).2
  have hLim :
      ∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∃ l : ℝ,
          Tendsto
            (fun k : ℕ => (ω (fastApproxSeq (E := E) n v hv x k) : ℝ)) atTop (nhds l) :=
    hAE (w := fastApproxSeq (E := E) n v hv x) (fun k => by simpa [sub_eq_add_neg] using hinc k)
  filter_upwards [hLim] with ω hω
  exact tendsto_nhds_limUnder hω

end AETendstoLimUnder

section EvalLimitOnRange

open OSforGFF.MinlosGaussianKolmogorov

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NuclearSpaceStd E]

open scoped BigOperators

/-- Core lemma behind `exists_ae_limUnder_eval_fastApproxSeq_eq_eval`: if we fix an index `n` such
that *every* square-summable `seminormFamily n`-sequence is evaluated a.s. to a sequence converging
to `0`, then the `limUnder` evaluation along a fast approximation of `toBanach f` recovers `ω f`
a.s. -/
theorem ae_limUnder_eval_fastApproxSeq_eq_eval_of_ae_tendsto_eval_atTop_nhds_zero
    {n : ℕ}
    (T : E →ₗ[ℝ] H)
    (hAE0 :
      ∀ u : ℕ → E,
        Summable (fun k : ℕ => (seminormFamily (E := E) n (u k)) ^ 2) →
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            Tendsto (fun k : ℕ => (ω (u k) : ℝ)) atTop (nhds 0))) :
    ∀ (v : ℕ → E)
      (hv : DenseRange fun k : ℕ =>
        toBanachOfSeminorm_seminormFamily (E := E) n (v k))
      (f : E),
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
          limUnder atTop (fun k : ℕ => (ω (fastApproxSeq (E := E) n v hv
            (toBanachOfSeminorm_seminormFamily (E := E) n f) k) : ℝ)) = ω f) := by
  intro v hv f
  let x : BanachOfSeminorm (E := E) (seminormFamily (E := E) n) :=
    toBanachOfSeminorm_seminormFamily (E := E) n f
  let w : ℕ → E := fastApproxSeq (E := E) n v hv x
  have hw_dist :
      ∀ k : ℕ,
        dist x (toBanachOfSeminorm_seminormFamily (E := E) n (w k))
          < (1 / (2 * ((k + 1 : ℕ) : ℝ) ^ 4)) :=
    (fastApproxSeq_spec (E := E) (n := n) (v := v) hv x).1
  -- Control `p_n (w k - f)` using the `BanachOfSeminorm` distance to `x`.
  have hpn :
      Summable (fun k : ℕ => (seminormFamily (E := E) n (w k - f)) ^ 2) := by
    have hle : ∀ k : ℕ, seminormFamily (E := E) n (w k - f) ≤ (1 / (2 * ((k + 1 : ℕ) : ℝ) ^ 4)) := by
      intro k
      have :
          dist (toBanachOfSeminorm_seminormFamily (E := E) n (w k))
              (toBanachOfSeminorm_seminormFamily (E := E) n f)
            < (1 / (2 * ((k + 1 : ℕ) : ℝ) ^ 4)) := by
        simpa [x, dist_comm] using hw_dist k
      have hdist :
          dist (toBanachOfSeminorm_seminormFamily (E := E) n (w k))
              (toBanachOfSeminorm_seminormFamily (E := E) n f)
            = seminormFamily (E := E) n (w k - f) := by
        simp [dist_toBanachOfSeminorm_seminormFamily (E := E) (n := n) (x := w k) (y := f),
          sub_eq_add_neg, add_comm]
      exact (le_of_lt (by simpa [hdist] using this))
    have hnonneg : ∀ k : ℕ, 0 ≤ (seminormFamily (E := E) n (w k - f)) ^ 2 := by
      intro k; exact sq_nonneg _
    have hle_sq :
        ∀ k : ℕ,
          (seminormFamily (E := E) n (w k - f)) ^ 2 ≤ (1 / (2 * ((k + 1 : ℕ) : ℝ) ^ 4)) ^ 2 := by
      intro k
      have hp_nonneg : 0 ≤ seminormFamily (E := E) n (w k - f) := apply_nonneg _ _
      exact pow_le_pow_left₀ hp_nonneg (hle k) 2
    have hsum_base :
        Summable (fun k : ℕ => (1 / (2 * ((k + 1 : ℕ) : ℝ) ^ 4)) ^ 2) := by
      have h0 : Summable (fun n : ℕ => (1 / ((n : ℝ) ^ (8 : ℕ)) : ℝ)) :=
        (Real.summable_one_div_nat_pow (p := 8)).2 (by decide)
      have h0' : Summable (fun k : ℕ => (1 / ((k + 1 : ℕ) : ℝ) ^ 8 : ℝ)) := by
        simpa using ((_root_.summable_nat_add_iff 1).2 h0)
      have hsum : Summable (fun k : ℕ => (1 / 4 : ℝ) * (1 / ((k + 1 : ℕ) : ℝ) ^ 8)) :=
        h0'.mul_left (1 / 4 : ℝ)
      refine hsum.congr ?_
      intro k
      have hk0 : ((k + 1 : ℕ) : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.succ_ne_zero k)
      field_simp [hk0]
      ring
    exact Summable.of_nonneg_of_le hnonneg hle_sq hsum_base
  have hAE_tendsto0 :
      ∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        Tendsto (fun k : ℕ => (ω (w k - f) : ℝ)) atTop (nhds 0) :=
    hAE0 (u := fun k => w k - f) hpn
  -- Package additivity so that `ω (w k - f) = ω (w k) - ω f`, hence `ω (w k) → ω f`.
  let v' : (ℕ ⊕ Unit) → E := fun s => Sum.rec (fun k => w k - f) (fun _ => f) s
  have hadd :
      ∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∀ i j : (ℕ ⊕ Unit), ω (v' i + v' j) = ω (v' i) + ω (v' j) := by
    simpa [v'] using (ae_eval_add_all (E := E) (H := H) (T := T) v')
  filter_upwards [hAE_tendsto0, hadd] with ω hω0 haddω
  have hwk : Tendsto (fun k : ℕ => (ω (w k) : ℝ)) atTop (nhds (ω f)) := by
    have hrewrite : (fun k : ℕ => (ω (w k) : ℝ) - ω f) =
        fun k : ℕ => (ω (w k - f) : ℝ) := by
      funext k
      have h1 : ω ((w k - f) + f) = ω (w k - f) + ω f := by
        simpa [v'] using haddω (Sum.inl k) (Sum.inr ())
      have hwkf : (w k - f) + f = w k := by abel
      have : (ω (w k) : ℝ) = ω (w k - f) + ω f := by simpa [hwkf] using h1
      linarith
    have : Tendsto (fun k : ℕ => (ω (w k) : ℝ) - ω f) atTop (nhds (0 : ℝ)) := by
      simpa [hrewrite] using hω0
    simpa [sub_eq_add_neg] using this.add_const (ω f)
  -- `limUnder` agrees with the limit under `Tendsto`.
  simpa [w, x] using (Filter.Tendsto.limUnder_eq hwk)

/-- Using the `limUnder`-definition along a fast approximation sequence, we recover the original
evaluation `ω f` almost surely when we evaluate at `toBanachOfSeminorm_seminormFamily n f`. -/
theorem exists_ae_limUnder_eval_fastApproxSeq_eq_eval
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ (v : ℕ → E)
        (hv : DenseRange fun k : ℕ =>
          toBanachOfSeminorm_seminormFamily (E := E) n (v k))
        (f : E),
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            limUnder atTop (fun k : ℕ => (ω (fastApproxSeq (E := E) n v hv
              (toBanachOfSeminorm_seminormFamily (E := E) n f) k) : ℝ)) = ω f) := by
  -- Choose the controlling seminorm from the Borel–Cantelli lemma.
  rcases exists_ae_tendsto_eval_atTop_nhds_zero_of_summable_seminormFamily_sq
      (E := E) (H := H) (T := T) h_sq with ⟨n, C, hC0, hAE0⟩
  refine ⟨n, C, hC0, ?_⟩
  exact ae_limUnder_eval_fastApproxSeq_eq_eval_of_ae_tendsto_eval_atTop_nhds_zero
    (E := E) (H := H) (T := T) (n := n) hAE0

end EvalLimitOnRange

section BanachExtensionMap

variable [NuclearSpaceStd E]

open scoped Topology

/-- For fixed `n` and a chosen dense sequence `v`, extend a sample path `ω : E → ℝ` to the local
Banach completion `BanachOfSeminorm (seminormFamily n)` by taking `limUnder` along a chosen fast
approximation sequence. -/
noncomputable
def evalOnBanach (n : ℕ) (v : ℕ → E)
    (hv : DenseRange fun k : ℕ =>
      toBanachOfSeminorm_seminormFamily (E := E) n (v k))
    (ω : E → ℝ) :
    BanachOfSeminorm (E := E) (seminormFamily (E := E) n) → ℝ := fun x =>
  limUnder atTop (fun k : ℕ => (ω (fastApproxSeq (E := E) n v hv x k) : ℝ))

/-- Measurability of the Banach-extension map `ω ↦ evalOnBanach … ω` into the product measurable
space on `BanachOfSeminorm (seminormFamily n) → ℝ`. -/
theorem measurable_evalOnBanach (n : ℕ) (v : ℕ → E)
    (hv : DenseRange fun k : ℕ =>
      toBanachOfSeminorm_seminormFamily (E := E) n (v k)) :
    Measurable fun ω : (E → ℝ) => evalOnBanach (E := E) n v hv ω := by
  -- Measurability into a Π-type is coordinatewise.
  refine measurable_pi_lambda _ (fun x => ?_)
  simpa [evalOnBanach] using
    measurable_limUnder_eval_fastApproxSeq (E := E) (n := n) (v := v) hv x

end BanachExtensionMap

section BanachExtensionAE

open OSforGFF.MinlosGaussianKolmogorov

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NuclearSpaceStd E]

-- Provide the canonical `ℚ`-module structure by restricting scalars along `ℚ →+* ℝ`.
local instance : Module ℚ E := Module.compHom E (algebraMap ℚ ℝ)

/-- If we have almost-sure vanishing on the kernel of `seminormFamily n`, then (a.s.) a sample path
on a countable ℚ-span factors through the quotient by `qSpanSeminormFamilyKer n`. -/
theorem ae_exists_qLinear_on_qSpan_quotient_seminormFamilyKer_of_ae_eval_eq_zero
    {n : ℕ} (T : E →ₗ[ℝ] H)
    (hker :
      ∀ f : E, seminormFamily (E := E) n f = 0 →
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T), (ω f : ℝ) = 0))
    (v : ℕ → E) :
    (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
      ∃ Lq :
        (Submodule.span ℚ (Set.range v) ⧸ qSpanSeminormFamilyKer (E := E) (v := v) n) →ₗ[ℚ] ℝ,
        ∀ x : Submodule.span ℚ (Set.range v),
          Lq ((qSpanSeminormFamilyKer (E := E) (v := v) n).mkQ x) = ω (x : E)) := by
  classical
  -- ℚ-linearity on the ℚ-span.
  have hLin :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∃ L : Submodule.span ℚ (Set.range v) →ₗ[ℚ] ℝ, ∀ x, L x = ω (x : E)) :=
    ae_exists_qLinear_on_qSpan (E := E) (H := H) (v := v) T
  -- Vanishing on the seminorm kernel, simultaneously on the countable span.
  have hKerAll :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∀ x : Submodule.span ℚ (Set.range v),
          seminormFamily (E := E) n (x : E) = 0 → ω (x : E) = 0) := by
    have hx :
        ∀ x : Submodule.span ℚ (Set.range v),
          ∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            seminormFamily (E := E) n (x : E) = 0 → ω (x : E) = 0 := by
      intro x
      simpa using (hker (x : E))
    exact (MeasureTheory.ae_all_iff).2 hx
  filter_upwards [hLin, hKerAll] with ω hωLin hωKer
  rcases hωLin with ⟨L, hL⟩
  let K : Submodule ℚ (Submodule.span ℚ (Set.range v)) :=
    qSpanSeminormFamilyKer (E := E) (v := v) n
  have hK : K ≤ LinearMap.ker L := by
    intro x hx
    have hx0 : seminormFamily (E := E) n (x : E) = 0 :=
      (mem_qSpanSeminormFamilyKer_iff (E := E) (v := v) n x).1 hx
    have : ω (x : E) = 0 := hωKer x hx0
    simpa [LinearMap.mem_ker, hL x] using this
  refine ⟨K.liftQ L hK, ?_⟩
  intro x
  simp [K, hL x]

/-- Restatement of `exists_ae_tendsto_limUnder_eval_fastApproxSeq` in terms of `evalOnBanach`. -/
theorem exists_ae_tendsto_evalOnBanach
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ (v : ℕ → E)
        (hv : DenseRange fun k : ℕ =>
          toBanachOfSeminorm_seminormFamily (E := E) n (v k))
        (x : BanachOfSeminorm (E := E) (seminormFamily (E := E) n)),
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            Tendsto
              (fun k : ℕ => (ω (fastApproxSeq (E := E) n v hv x k) : ℝ)) atTop
              (nhds (evalOnBanach (E := E) n v hv ω x))) := by
  simpa [evalOnBanach] using
    exists_ae_tendsto_limUnder_eval_fastApproxSeq (E := E) (H := H) (T := T) h_sq

/-- Restatement of `exists_ae_limUnder_eval_fastApproxSeq_eq_eval` in terms of `evalOnBanach`. -/
theorem exists_ae_evalOnBanach_toBanach_eq_eval
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ (v : ℕ → E)
        (hv : DenseRange fun k : ℕ =>
          toBanachOfSeminorm_seminormFamily (E := E) n (v k))
        (f : E),
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            evalOnBanach (E := E) n v hv ω
                (toBanachOfSeminorm_seminormFamily (E := E) n f) = ω f) := by
  simpa [evalOnBanach] using
    exists_ae_limUnder_eval_fastApproxSeq_eq_eval (E := E) (H := H) (T := T) h_sq

/-- Using the same controlling seminorm index as in
`exists_ae_tendsto_eval_atTop_nhds_zero_of_summable_seminormFamily_sq`, we get almost-sure
vanishing on the seminorm kernel (by applying the convergence statement to a constant sequence). -/
theorem exists_ae_eval_eq_zero_of_seminormFamily_eq_zero'
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ f : E, seminormFamily (E := E) n f = 0 →
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T), (ω f : ℝ) = 0) := by
  classical
  rcases
      exists_ae_tendsto_eval_atTop_nhds_zero_of_summable_seminormFamily_sq
        (E := E) (H := H) (T := T) h_sq with
    ⟨n, C, hC0, h_tendsto⟩
  refine ⟨n, C, hC0, ?_⟩
  intro f hf0
  -- Apply the convergence lemma to the constant sequence `u k = f`.
  have hsum : Summable (fun _k : ℕ => (seminormFamily (E := E) n f) ^ 2) := by
    simpa [hf0]
  have hAE :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        Tendsto (fun _k : ℕ => (ω f : ℝ)) atTop (nhds 0)) := by
    simpa using (h_tendsto (u := fun _k : ℕ => f) hsum)
  filter_upwards [hAE] with ω hω
  -- A constant sequence converges to its value, hence the value is `0`.
  have : (ω f : ℝ) = 0 := by
    have hlim : Tendsto (fun _k : ℕ => (ω f : ℝ)) atTop (nhds (ω f)) := tendsto_const_nhds
    exact tendsto_nhds_unique hlim hω
  exact this

/-- With the same controlling seminorm index `n` as in
`exists_ae_eval_eq_zero_of_seminormFamily_eq_zero'`, we can package (a.s.) a ℚ-linear realization
on the ℚ-span that factors through the quotient by the seminorm kernel. -/
theorem exists_ae_qLinear_on_qSpan_quotient_seminormFamilyKer'
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ (v : ℕ → E),
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
          ∃ Lq :
            (Submodule.span ℚ (Set.range v) ⧸
                qSpanSeminormFamilyKer (E := E) (v := v) n) →ₗ[ℚ] ℝ,
            ∀ x : Submodule.span ℚ (Set.range v),
              Lq ((qSpanSeminormFamilyKer (E := E) (v := v) n).mkQ x) = ω (x : E)) := by
  classical
  rcases exists_ae_eval_eq_zero_of_seminormFamily_eq_zero' (E := E) (H := H) (T := T) h_sq with
    ⟨n, C, hC0, hker⟩
  refine ⟨n, C, hC0, ?_⟩
  intro v
  -- ℚ-linearity on the ℚ-span.
  have hLin :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∃ L : Submodule.span ℚ (Set.range v) →ₗ[ℚ] ℝ, ∀ x, L x = ω (x : E)) :=
    ae_exists_qLinear_on_qSpan (E := E) (H := H) (v := v) T
  -- Vanishing on the seminorm kernel, simultaneously on the countable span.
  have hKerAll :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∀ x : Submodule.span ℚ (Set.range v),
          seminormFamily (E := E) n (x : E) = 0 → ω (x : E) = 0) := by
    have hx :
        ∀ x : Submodule.span ℚ (Set.range v),
          ∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            seminormFamily (E := E) n (x : E) = 0 → ω (x : E) = 0 := by
      intro x
      simpa using (hker (x : E))
    exact (MeasureTheory.ae_all_iff).2 hx
  filter_upwards [hLin, hKerAll] with ω hωLin hωKer
  rcases hωLin with ⟨L, hL⟩
  let K : Submodule ℚ (Submodule.span ℚ (Set.range v)) :=
    qSpanSeminormFamilyKer (E := E) (v := v) n
  have hK : K ≤ LinearMap.ker L := by
    intro x hx
    have hx0 : seminormFamily (E := E) n (x : E) = 0 :=
      (mem_qSpanSeminormFamilyKer_iff (E := E) (v := v) n x).1 hx
    have : ω (x : E) = 0 := hωKer x hx0
    -- Transfer via the realization `hL`.
    simpa [LinearMap.mem_ker, hL x] using this
  refine ⟨K.liftQ L hK, ?_⟩
  intro x
  -- `liftQ` agrees with `L`, and `L` agrees with `ω` on representatives.
  simp [K, hL x]

/-- A convenient “one-shot” choice of the controlling seminorm index `n` for the support step:

* square-summable `seminormFamily n`-sequences evaluate a.s. to sequences tending to `0`;
* this implies a.s. vanishing on the seminorm kernel;
* and hence (a.s.) a ℚ-linear realization on any countable ℚ-span factors through the quotient;
* moreover, the Banach extension `evalOnBanach` agrees with the original evaluation on that span
  simultaneously almost surely. -/
theorem exists_control_seminorm_for_qSpan_and_evalOnBanach
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      (∀ u : ℕ → E,
        Summable (fun k : ℕ => (seminormFamily (E := E) n (u k)) ^ 2) →
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            Tendsto (fun k : ℕ => (ω (u k) : ℝ)) atTop (nhds 0))) ∧
      (∀ f : E, seminormFamily (E := E) n f = 0 →
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T), (ω f : ℝ) = 0)) ∧
      (∀ v : ℕ → E,
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
          ∃ Lq :
            (Submodule.span ℚ (Set.range v) ⧸
                qSpanSeminormFamilyKer (E := E) (v := v) n) →ₗ[ℚ] ℝ,
            ∀ x : Submodule.span ℚ (Set.range v),
              Lq ((qSpanSeminormFamilyKer (E := E) (v := v) n).mkQ x) = ω (x : E))) ∧
      (∀ (v : ℕ → E)
        (hv : DenseRange fun k : ℕ =>
          toBanachOfSeminorm_seminormFamily (E := E) n (v k)),
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
          ∀ x : Submodule.span ℚ (Set.range v),
            evalOnBanach (E := E) n v hv ω
                (toBanachOfSeminorm_seminormFamily (E := E) n (x : E)) = ω (x : E))) := by
  classical
  -- Pick `n` from the Borel–Cantelli convergence statement.
  rcases
      exists_ae_tendsto_eval_atTop_nhds_zero_of_summable_seminormFamily_sq
        (E := E) (H := H) (T := T) h_sq with
    ⟨n, C, hC0, hAE0⟩
  refine ⟨n, C, hC0, hAE0, ?_, ?_, ?_⟩
  · -- Kernel vanishing from the constant sequence argument.
    intro f hf0
    have hsum : Summable (fun _k : ℕ => (seminormFamily (E := E) n f) ^ 2) := by
      simpa [hf0]
    have hAE :
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
          Tendsto (fun _k : ℕ => (ω f : ℝ)) atTop (nhds 0)) := by
      simpa using (hAE0 (u := fun _k : ℕ => f) hsum)
    filter_upwards [hAE] with ω hω
    have hlim : Tendsto (fun _k : ℕ => (ω f : ℝ)) atTop (nhds (ω f)) := tendsto_const_nhds
    exact tendsto_nhds_unique hlim hω
  · -- Quotient factorization on qSpans, using the kernel vanishing we just proved.
    intro v
    have hker :
        ∀ f : E, seminormFamily (E := E) n f = 0 →
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T), (ω f : ℝ) = 0) := by
      intro f hf0; exact (by
        -- reuse the previous step
        have := (show
          ∀ f : E, seminormFamily (E := E) n f = 0 →
            (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T), (ω f : ℝ) = 0) from by
              intro f hf0
              -- kernel vanishing proved above in the previous goal
              -- (duplicated here to keep proof local)
              have hsum : Summable (fun _k : ℕ => (seminormFamily (E := E) n f) ^ 2) := by
                simpa [hf0]
              have hAE :
                  (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
                    Tendsto (fun _k : ℕ => (ω f : ℝ)) atTop (nhds 0)) := by
                simpa using (hAE0 (u := fun _k : ℕ => f) hsum)
              filter_upwards [hAE] with ω hω
              have hlim : Tendsto (fun _k : ℕ => (ω f : ℝ)) atTop (nhds (ω f)) := tendsto_const_nhds
              exact tendsto_nhds_unique hlim hω
          ) f hf0
        exact this)
    exact
      ae_exists_qLinear_on_qSpan_quotient_seminormFamilyKer_of_ae_eval_eq_zero
        (E := E) (H := H) (n := n) (T := T) hker v
  · -- Agreement of `evalOnBanach` with evaluation on the ℚ-span (simultaneously).
    intro v hv
    have hpoint :
        ∀ x : Submodule.span ℚ (Set.range v),
          (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
            evalOnBanach (E := E) n v hv ω
                (toBanachOfSeminorm_seminormFamily (E := E) n (x : E)) = ω (x : E)) := by
      intro x
      -- This is exactly the `limUnder` recovery lemma, rewritten via `evalOnBanach`.
      simpa [evalOnBanach] using
        (ae_limUnder_eval_fastApproxSeq_eq_eval_of_ae_tendsto_eval_atTop_nhds_zero
          (E := E) (H := H) (T := T) (n := n) hAE0 (v := v) (hv := hv) (f := (x : E)))
    simpa using (MeasureTheory.ae_all_iff.2 hpoint)

/-- Under the common control index from
`exists_control_seminorm_for_qSpan_and_evalOnBanach`, the Banach extension `evalOnBanach` factors
through the quotient on the dense ℚ-span (a.s.). -/
theorem exists_ae_qSpanQuotientMap_agrees_evalOnBanach
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ (v : ℕ → E)
        (hv : DenseRange fun k : ℕ =>
          toBanachOfSeminorm_seminormFamily (E := E) n (v k)),
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
          ∃ Lq :
            (Submodule.span ℚ (Set.range v) ⧸
                qSpanSeminormFamilyKer (E := E) (v := v) n) →ₗ[ℚ] ℝ,
            ∀ x : Submodule.span ℚ (Set.range v),
              Lq ((qSpanSeminormFamilyKer (E := E) (v := v) n).mkQ x) =
                evalOnBanach (E := E) n v hv ω
                  (toBanachOfSeminorm_seminormFamily (E := E) n (x : E))) := by
  classical
  rcases exists_control_seminorm_for_qSpan_and_evalOnBanach (E := E) (H := H) (T := T) h_sq with
    ⟨n, C, hC0, _hAE0, _hker, hquot, heval⟩
  refine ⟨n, C, hC0, ?_⟩
  intro v hv
  have hquot' :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∃ Lq :
          (Submodule.span ℚ (Set.range v) ⧸
              qSpanSeminormFamilyKer (E := E) (v := v) n) →ₗ[ℚ] ℝ,
          ∀ x : Submodule.span ℚ (Set.range v),
            Lq ((qSpanSeminormFamilyKer (E := E) (v := v) n).mkQ x) = ω (x : E)) :=
    hquot v
  have heval' :
      (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
        ∀ x : Submodule.span ℚ (Set.range v),
          evalOnBanach (E := E) n v hv ω
              (toBanachOfSeminorm_seminormFamily (E := E) n (x : E)) = ω (x : E)) :=
    heval v hv
  filter_upwards [hquot', heval'] with ω hq he
  rcases hq with ⟨Lq, hLq⟩
  refine ⟨Lq, ?_⟩
  intro x
  calc
    Lq ((qSpanSeminormFamilyKer (E := E) (v := v) n).mkQ x) = ω (x : E) := hLq x
    _ = evalOnBanach (E := E) n v hv ω
          (toBanachOfSeminorm_seminormFamily (E := E) n (x : E)) := by
          simpa using (he x).symm

/-- On the **countable** ℚ-span of a dense sequence, the Banach extension agrees with the original
evaluation simultaneously almost surely. -/
theorem exists_ae_evalOnBanach_toBanach_eq_eval_on_qSpan
    (T : E →ₗ[ℝ] H)
    (h_sq : Continuous fun f : E => (‖T f‖ ^ 2 : ℝ)) :
    ∃ n : ℕ, ∃ C : ℝ≥0, C ≠ 0 ∧
      ∀ (v : ℕ → E)
        (hv : DenseRange fun k : ℕ =>
          toBanachOfSeminorm_seminormFamily (E := E) n (v k)),
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
          ∀ x : Submodule.span ℚ (Set.range v),
            evalOnBanach (E := E) n v hv ω
                (toBanachOfSeminorm_seminormFamily (E := E) n (x : E)) = ω (x : E)) := by
  classical
  rcases exists_ae_evalOnBanach_toBanach_eq_eval (E := E) (H := H) (T := T) h_sq with
    ⟨n, C, hC0, hAE⟩
  refine ⟨n, C, hC0, ?_⟩
  intro v hv
  -- Use countability of the ℚ-span to upgrade pointwise a.s. equality to simultaneous equality.
  have hpoint :
      ∀ x : Submodule.span ℚ (Set.range v),
        (∀ᵐ ω ∂(gaussianProcess (E := E) (H := H) T),
          evalOnBanach (E := E) n v hv ω
              (toBanachOfSeminorm_seminormFamily (E := E) n (x : E)) = ω (x : E)) := by
    intro x
    simpa using (hAE (v := v) (hv := hv) (f := (x : E)))
  simpa using (MeasureTheory.ae_all_iff.2 hpoint)

end BanachExtensionAE

end MinlosGaussianSupport

end

end OSforGFF
