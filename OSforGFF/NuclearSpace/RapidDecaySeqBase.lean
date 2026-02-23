/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.InnerProductSpace.l2Space

import OSforGFF.NuclearSpace.Defs
import OSforGFF.NuclearSpace.Std

/-!
# A general rapidly decreasing sequence model (weighted `ℓ²`)

This file is a parameterized variant of `OSforGFF.NuclearSpace.RapidDecaySeq`:
we build a nuclear Fréchet space of sequences `f : ℕ → ℝ` such that, for every `k : ℕ`,
the weighted sequence `n ↦ (base n)^k * f n` is in `ℓ²`.

The goal is to support *multi-index* coefficient models (e.g. Hermite expansions) without
duplicating the entire nuclearity proof: one can choose `base` encoding a multi-index weight and
prove a single summability condition `∑ (base n)⁻² < ∞`, then obtain `NuclearSpaceStd`.

Nothing in this file relies on any Schwartz-specific axiom.
-/

open scoped BigOperators NNReal ENNReal

namespace OSforGFF

noncomputable section

/-! ## The space of weighted rapidly decreasing sequences -/

namespace RapidDecaySeqBase

local notation "H" => ℓ²(ℕ, ℝ)

variable (base : ℕ → ℝ)

/-- The weights \(w_k(n) = (base\ n)^k\). -/
def weight (k : ℕ) (n : ℕ) : ℝ := (base n) ^ k

/-- Pointwise weighting of a sequence by `weight`. -/
def weightFun (k : ℕ) (f : ℕ → ℝ) : ℕ → ℝ := fun n => weight base k n * f n

@[simp] lemma weight_zero (n : ℕ) : weight base 0 n = 1 := by
  simp [weight]

@[simp] lemma weight_succ (k n : ℕ) :
    weight base (k + 1) n = weight base k n * base n := by
  simp [weight, pow_succ]

/-- The submodule of sequences whose weighted versions are in `ℓ²` for every weight. -/
def space : Submodule ℝ (ℕ → ℝ) where
  carrier := { f | ∀ k : ℕ, Memℓp (weightFun base k f) (2 : ℝ≥0∞) }
  zero_mem' := by
    intro k
    have h0 : weightFun base k (0 : ℕ → ℝ) = 0 := by
      funext n
      simp [weightFun]
    simpa [h0] using (zero_memℓp (E := fun _ : ℕ => ℝ) (p := (2 : ℝ≥0∞)))
  add_mem' := by
    intro f g hf hg k
    have hfg : weightFun base k (f + g) = weightFun base k f + weightFun base k g := by
      funext n
      simp [weightFun, mul_add]
    simpa [hfg] using (hf k).add (hg k)
  smul_mem' := by
    intro c f hf k
    have hsmul : weightFun base k (c • f) = c • weightFun base k f := by
      funext n
      simp [weightFun, mul_assoc, mul_comm]
    simpa [hsmul] using (hf k).const_smul c

/-! We use `space base` as a **type** via the coercion `Submodule → Sort`. -/

namespace Space

variable (k : ℕ)

/-- The canonical map to `ℓ²`: send a rapidly decreasing sequence to its `k`-weighted version. -/
noncomputable def toL2ₗ : (space base) →ₗ[ℝ] H where
  toFun x := ⟨weightFun base k x.1, x.2 k⟩
  map_add' x y := by
    ext n
    simp [weightFun, mul_add]
  map_smul' c x := by
    ext n
    simp [weightFun, mul_left_comm]

@[simp] lemma toL2ₗ_apply (x : space base) (n : ℕ) :
    (toL2ₗ (base := base) k x : ℕ → ℝ) n = weight base k n * x.1 n := rfl

/-- The weighted `ℓ²` seminorms generating the Fréchet topology. -/
noncomputable def seminorm : Seminorm ℝ (space base) :=
  (normSeminorm ℝ H).comp (toL2ₗ (base := base) k)

@[simp] lemma seminorm_apply (x : space base) :
    seminorm (base := base) k x = ‖toL2ₗ (base := base) k x‖ := by
  rfl

variable {base}

theorem seminorm_mono (hbase : ∀ n, (1 : ℝ) ≤ base n) :
    Monotone (fun k : ℕ => seminorm (base := base) k) := by
  intro a b hab x
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  let A : H := toL2ₗ (base := base) a x
  let B : H := toL2ₗ (base := base) b x
  have hAB : ‖A‖ ≤ ‖B‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := ‖B‖) (by positivity) ?_
    intro s
    have hpoint : ∀ n, ‖A n‖ ^ ((2 : ℝ≥0∞).toReal) ≤ ‖B n‖ ^ ((2 : ℝ≥0∞).toReal) := by
      intro n
      have hle_w : weight base a n ≤ weight base b n := by
        simpa [weight] using (pow_le_pow_right₀ (hbase n) hab)
      have hn : 0 ≤ weight base a n := by
        have : 0 ≤ base n := (zero_le_one.trans (hbase n))
        simpa [weight] using pow_nonneg this a
      have hn' : 0 ≤ weight base b n := by
        have : 0 ≤ base n := (zero_le_one.trans (hbase n))
        simpa [weight] using pow_nonneg this b
      have habs : ‖(weight base a n * x.1 n)‖ ≤ ‖(weight base b n * x.1 n)‖ := by
        simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hn, abs_of_nonneg hn'] using
          mul_le_mul_of_nonneg_right hle_w (abs_nonneg (x.1 n))
      have : (‖weight base a n * x.1 n‖) ^ ((2 : ℝ≥0∞).toReal)
            ≤ (‖weight base b n * x.1 n‖) ^ ((2 : ℝ≥0∞).toReal) := by
        exact Real.rpow_le_rpow (norm_nonneg _) habs (by norm_num)
      simpa [A, B, toL2ₗ_apply] using this
    calc
      ∑ i ∈ s, ‖A i‖ ^ ((2 : ℝ≥0∞).toReal)
          ≤ ∑ i ∈ s, ‖B i‖ ^ ((2 : ℝ≥0∞).toReal) := by
              exact Finset.sum_le_sum fun i hi => hpoint i
      _ ≤ ‖B‖ ^ ((2 : ℝ≥0∞).toReal) := by
            simpa using (lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) hp B s)
  simpa [seminorm, A, B] using hAB

/-! ## Topology generated by the seminorms -/

noncomputable instance (priority := 2000) : TopologicalSpace (space base) :=
  (SeminormFamily.moduleFilterBasis (𝕜 := ℝ) (F := space base)
      (p := fun k => seminorm (base := base) k)).topology

theorem withSeminorms : WithSeminorms (fun k : ℕ => seminorm (base := base) k) := by
  exact ⟨rfl⟩

/-! ## A diagonal nuclear operator on `ℓ²` -/

/-- Coefficients \(\sigma_s(n) = (base\ n)^{-s}\). -/
def sigma (s : ℕ) (n : ℕ) : ℝ := (weight base s n)⁻¹

@[simp] lemma sigma_apply (s n : ℕ) : sigma (base := base) s n = (weight base s n)⁻¹ := rfl

lemma abs_sigma_le_one (hbase : ∀ n, (1 : ℝ) ≤ base n) (s n : ℕ) :
    |sigma (base := base) s n| ≤ 1 := by
  have hpos : 0 < weight base s n := by
    have : 0 < base n := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hbase n)
    simpa [weight] using (pow_pos this s)
  have hone : (1 : ℝ) ≤ weight base s n := by
    simpa [weight] using (one_le_pow₀ (a := base n) (hbase n) (n := s))
  have : (weight base s n)⁻¹ ≤ 1 := by
    simpa [one_div] using (inv_le_one_of_one_le₀ hone)
  simpa [sigma, abs_of_pos (inv_pos_of_pos hpos)] using this

/-- The diagonal linear map on `ℓ²` given by multiplying coordinates by `sigma s`. -/
noncomputable def diagPowInvₗ (hbase : ∀ n, (1 : ℝ) ≤ base n) (s : ℕ) : H →ₗ[ℝ] H where
  toFun x :=
    ⟨fun n => sigma (base := base) s n * x n, by
      have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
      have hx : Summable (fun n : ℕ => ‖x n‖ ^ ((2 : ℝ≥0∞).toReal)) :=
        (lp.memℓp x).summable hp
      have hnonneg : ∀ n : ℕ, 0 ≤ ‖sigma (base := base) s n * x n‖ ^ ((2 : ℝ≥0∞).toReal) := by
        intro n; positivity
      have hle : ∀ n : ℕ,
          ‖sigma (base := base) s n * x n‖ ^ ((2 : ℝ≥0∞).toReal) ≤ ‖x n‖ ^ ((2 : ℝ≥0∞).toReal) := by
        intro n
        have : ‖sigma (base := base) s n * x n‖ ≤ ‖x n‖ := by
          have hs : ‖sigma (base := base) s n‖ ≤ 1 := by
            simpa [Real.norm_eq_abs] using abs_sigma_le_one (base := base) hbase s n
          calc
            ‖sigma (base := base) s n * x n‖ = ‖sigma (base := base) s n‖ * ‖x n‖ := by
              simp [norm_mul]
            _ ≤ 1 * ‖x n‖ := by gcongr
            _ = ‖x n‖ := by simp
        exact Real.rpow_le_rpow (norm_nonneg _) this (by norm_num)
      refine memℓp_gen (p := (2 : ℝ≥0∞)) ?_
      exact Summable.of_nonneg_of_le hnonneg hle hx⟩
  map_add' x y := by
    ext n
    change sigma (base := base) s n * (x n + y n) =
      sigma (base := base) s n * x n + sigma (base := base) s n * y n
    simp [mul_add]
  map_smul' c x := by
    ext n
    simp [mul_left_comm]

@[simp] lemma diagPowInvₗ_apply (hbase : ∀ n, (1 : ℝ) ≤ base n) (s : ℕ) (x : H) (n : ℕ) :
    (diagPowInvₗ (base := base) hbase s x : ℕ → ℝ) n = sigma (base := base) s n * x n := rfl

/-- The diagonal continuous linear map on `ℓ²` given by multiplying coordinates by `sigma s`. -/
noncomputable def diagPowInvCLM (hbase : ∀ n, (1 : ℝ) ≤ base n) (s : ℕ) : H →L[ℝ] H := by
  refine (diagPowInvₗ (base := base) hbase s).mkContinuous 1 ?_
  intro x
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  let y : H := diagPowInvₗ (base := base) hbase s x
  have hy : ‖y‖ ≤ ‖x‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := ‖x‖) (by positivity) ?_
    intro t
    have hle_term : ∀ n : ℕ, ‖y n‖ ^ ((2 : ℝ≥0∞).toReal) ≤ ‖x n‖ ^ ((2 : ℝ≥0∞).toReal) := by
      intro n
      have : ‖y n‖ ≤ ‖x n‖ := by
        have hs' : ‖sigma (base := base) s n‖ ≤ 1 := by
          simpa [Real.norm_eq_abs] using abs_sigma_le_one (base := base) hbase s n
        calc
          ‖y n‖ = ‖sigma (base := base) s n * x n‖ := by
              simp [y, diagPowInvₗ_apply]
          _ = ‖sigma (base := base) s n‖ * ‖x n‖ := by simp [norm_mul]
          _ ≤ 1 * ‖x n‖ := by gcongr
          _ = ‖x n‖ := by simp
      exact Real.rpow_le_rpow (norm_nonneg _) this (by norm_num)
    calc
      ∑ i ∈ t, ‖y i‖ ^ ((2 : ℝ≥0∞).toReal)
          ≤ ∑ i ∈ t, ‖x i‖ ^ ((2 : ℝ≥0∞).toReal) := by
              exact Finset.sum_le_sum fun i hi => hle_term i
      _ ≤ ‖x‖ ^ ((2 : ℝ≥0∞).toReal) := by
            simpa using (lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) hp x t)
  simpa [y] using (hy.trans_eq (by simp))

@[simp] lemma diagPowInvCLM_apply (hbase : ∀ n, (1 : ℝ) ≤ base n) (s : ℕ) (x : H) (n : ℕ) :
    (diagPowInvCLM (base := base) hbase s x : ℕ → ℝ) n = sigma (base := base) s n * x n := rfl

/-! ### Nuclearity of the diagonal map from an `ℓ¹` hypothesis -/

theorem isNuclearMap_diagPowInvCLM_of_summable (hbase : ∀ n, (1 : ℝ) ≤ base n) (s : ℕ)
    (hsum : Summable (fun n : ℕ => ‖sigma (base := base) s n‖)) :
    IsNuclearMap (diagPowInvCLM (base := base) hbase s) := by
  haveI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let e : ℕ → H := fun n => lp.single (E := fun _ : ℕ => ℝ) 2 n (1 : ℝ)
  let φ : ℕ → (H →L[ℝ] ℝ) := fun n => innerSL ℝ (e n)
  let y : ℕ → H := fun n => (sigma (base := base) s n) • e n
  refine ⟨φ, y, ?_, ?_⟩
  · have hφ : ∀ n, ‖φ n‖ = 1 := by
      intro n
      have he : ‖e n‖ = 1 := by
        simp [e]
      calc
        ‖φ n‖ = ‖e n‖ := by
          simp [φ]
        _ = 1 := he
    have hy : ∀ n, ‖y n‖ = ‖sigma (base := base) s n‖ := by
      intro n
      have : ‖e n‖ = 1 := by
        simp [e]
      simp [y, this, norm_smul]
    refine (hsum.congr ?_)
    intro n
    simp [hφ n, hy n]
  · intro x
    have hx :
        HasSum (fun n : ℕ => lp.single 2 n ((diagPowInvCLM (base := base) hbase s x) n))
          (diagPowInvCLM (base := base) hbase s x) :=
      lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top
        (diagPowInvCLM (base := base) hbase s x)
    have hterm : ∀ n : ℕ, lp.single 2 n ((diagPowInvCLM (base := base) hbase s x) n) = (φ n x) • y n := by
      intro n
      have hφx : φ n x = x n := by
        simpa [φ, e, innerSL_apply_apply] using
          (lp.inner_single_left (𝕜 := ℝ) (ι := ℕ) (G := fun _ : ℕ => ℝ) n (1 : ℝ) x)
      have hs' :
          lp.single (E := fun _ : ℕ => ℝ) (2 : ℝ≥0∞) n ((weight base s n)⁻¹ * x n) =
            ((weight base s n)⁻¹ * x n) • lp.single (E := fun _ : ℕ => ℝ) (2 : ℝ≥0∞) n (1 : ℝ) := by
        simpa using
          (lp.single_smul (E := fun _ : ℕ => ℝ) (p := (2 : ℝ≥0∞)) n ((weight base s n)⁻¹ * x n) (1 : ℝ))
      simp [y, e, diagPowInvCLM_apply, hφx, hs', sigma, smul_smul,
        mul_comm]
    have hx' : HasSum (fun n : ℕ => (φ n x) • y n) (diagPowInvCLM (base := base) hbase s x) :=
      HasSum.congr_fun hx (fun n => (hterm n).symm)
    exact hx'.tsum_eq.symm

/-!
## `space base` is a standard nuclear Fréchet space (under a summability hypothesis)

We reuse the same strategy as in `OSforGFF.NuclearSpace.RapidDecaySeq`:
- identify the local Banach spaces with `ℓ²` via the weighted maps;
- show the local inclusion from level `k+2` to level `k` is conjugate to a diagonal operator;
- conclude nuclearity from `∑ (base n)⁻² < ∞`.
-/

open scoped Topology

-- Force quotient topology to be the norm-induced one (see `RapidDecaySeq.lean` for discussion).
local instance (priority := 1001) (k : ℕ) :
    TopologicalSpace (QuotBySeminorm (E := space base) (seminorm (base := base) k)) :=
  (PseudoMetricSpace.toUniformSpace.toTopologicalSpace :
    TopologicalSpace (QuotBySeminorm (E := space base) (seminorm (base := base) k)))

noncomputable def toL2Quotₗ (k : ℕ) :
    QuotBySeminorm (E := space base) (seminorm (base := base) k) →ₗ[ℝ] H :=
  (seminormKer (E := space base) (p := seminorm (base := base) k)).liftQ (toL2ₗ (base := base) k) (by
    intro x hx
    have hx0 : seminorm (base := base) k x = 0 := hx
    have : ‖toL2ₗ (base := base) k x‖ = 0 := by
      simpa [seminorm_apply] using hx0
    exact (norm_eq_zero.mp this))

@[simp] lemma toL2Quotₗ_mk (k : ℕ) (x : space base) :
    toL2Quotₗ (base := base) k
      (Submodule.Quotient.mk (p := seminormKer (E := space base) (p := seminorm (base := base) k)) x) =
        toL2ₗ (base := base) k x := by
  simp [toL2Quotₗ]

lemma norm_toL2Quotₗ (k : ℕ) (x : QuotBySeminorm (E := space base) (seminorm (base := base) k)) :
    ‖toL2Quotₗ (base := base) k x‖ = ‖x‖ := by
  refine Submodule.Quotient.induction_on
    (p := seminormKer (E := space base) (p := seminorm (base := base) k)) x ?_
  intro y
  have hy_norm :
      ‖(Submodule.Quotient.mk
          (p := seminormKer (E := space base) (p := seminorm (base := base) k)) y :
        QuotBySeminorm (E := space base) (seminorm (base := base) k))‖ =
        seminorm (base := base) k y := by
    simpa using (QuotBySeminorm.norm_mk (E := space base) (p := seminorm (base := base) k) y)
  calc
    ‖toL2Quotₗ (base := base) k
        (Submodule.Quotient.mk (p := seminormKer (E := space base) (p := seminorm (base := base) k)) y)‖
        = ‖toL2ₗ (base := base) k y‖ := by simp [toL2Quotₗ_mk]
    _ = seminorm (base := base) k y := by simp [seminorm_apply]
    _ = ‖(Submodule.Quotient.mk
            (p := seminormKer (E := space base) (p := seminorm (base := base) k)) y :
          QuotBySeminorm (E := space base) (seminorm (base := base) k))‖ := by
        simp [hy_norm]

lemma denseRange_toL2ₗ (hbase : ∀ n, (1 : ℝ) ≤ base n) (k : ℕ) :
    DenseRange (toL2ₗ (base := base) k) := by
  intro y
  haveI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hy_hasSum :
      HasSum (fun n : ℕ => lp.single (E := fun _ : ℕ => ℝ) (2 : ℝ≥0∞) n (y n)) y :=
    lp.hasSum_single (E := fun _ : ℕ => ℝ) (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top y
  have hy_tendsto :
      Filter.Tendsto
        (fun N : ℕ =>
          ∑ n ∈ Finset.range N,
            lp.single (E := fun _ : ℕ => ℝ) (2 : ℝ≥0∞) n (y n))
        Filter.atTop (nhds y) :=
    hy_hasSum.tendsto_sum_nat
  have h_mem_range :
      ∀ N : ℕ,
        (∑ n ∈ Finset.range N, lp.single (E := fun _ : ℕ => ℝ) (2 : ℝ≥0∞) n (y n))
          ∈ Set.range (toL2ₗ (base := base) k) := by
    intro N
    let f : ℕ → ℝ := fun n => if n < N then (weight base k n)⁻¹ * y n else 0
    have hf : ∀ j : ℕ, Memℓp (weightFun base j f) (2 : ℝ≥0∞) := by
      intro j
      have hsum :
          Summable (fun n : ℕ => ‖(weightFun base j f) n‖ ^ ((2 : ℝ≥0∞).toReal)) := by
        refine summable_of_finite_support <| (Set.finite_Iio N).subset ?_
        intro n hn
        have : n < N := by
          by_contra hge
          have hn' : ¬ n < N := hge
          have hf0 : f n = 0 := by simp [f, hn']
          have : (weightFun base j f) n = 0 := by simp [weightFun, hf0]
          have : (‖(weightFun base j f) n‖ ^ ((2 : ℝ≥0∞).toReal)) = 0 := by
            simp [this]
          exact hn (by simpa using this)
        exact this
      exact memℓp_gen (p := (2 : ℝ≥0∞)) hsum
    let xN : space base := ⟨f, hf⟩
    refine ⟨xN, ?_⟩
    ext n
    by_cases hn : n < N
    · have hn0 : base n ≠ 0 := by
        have : (0 : ℝ) < base n := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hbase n)
        exact this.ne'
      have hne : weight base k n ≠ 0 := by
        simpa [weight] using (pow_ne_zero k hn0)
      have : (toL2ₗ (base := base) k xN : ℕ → ℝ) n = y n := by
        calc
          (toL2ₗ (base := base) k xN : ℕ → ℝ) n = weight base k n * ((weight base k n)⁻¹ * y n) := by
            simp [toL2ₗ_apply, xN, f, hn]
          _ = y n := by
            rw [← mul_assoc (weight base k n) (weight base k n)⁻¹ (y n)]
            simp [hne]
      simp [this, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single, Finset.mem_range, hn]
    · have hn' : ¬ n < N := hn
      have : (toL2ₗ (base := base) k xN : ℕ → ℝ) n = 0 := by
        simp [toL2ₗ_apply, xN, f, hn']
      simp [this, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single, Finset.mem_range, hn']
  refine mem_closure_of_tendsto hy_tendsto (Filter.Eventually.of_forall h_mem_range)

lemma denseRange_toL2Quotₗ (hbase : ∀ n, (1 : ℝ) ≤ base n) (k : ℕ) :
    DenseRange (toL2Quotₗ (base := base) k) := by
  intro y
  have hy : y ∈ closure (Set.range (toL2ₗ (base := base) k)) :=
    denseRange_toL2ₗ (base := base) hbase (k := k) y
  have hrange : Set.range (toL2ₗ (base := base) k) = Set.range (toL2Quotₗ (base := base) k) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨Submodule.Quotient.mk
        (p := seminormKer (E := space base) (p := seminorm (base := base) k)) x, ?_⟩
      simp [toL2Quotₗ_mk]
    · rintro ⟨x, rfl⟩
      refine Submodule.Quotient.induction_on
        (p := seminormKer (E := space base) (p := seminorm (base := base) k)) x ?_
      intro x
      exact ⟨x, by simp [toL2Quotₗ_mk]⟩
  simpa [hrange] using hy

lemma norm_coe_banachOfSeminorm
    (p : Seminorm ℝ (space base)) (x : QuotBySeminorm (E := space base) p) :
    ‖(x : BanachOfSeminorm (E := space base) p)‖ = ‖x‖ := by
  have hIso :
      Isometry ((↑) :
        QuotBySeminorm (E := space base) p → BanachOfSeminorm (E := space base) p) :=
    UniformSpace.Completion.coe_isometry
  have hdist := hIso.dist_eq x (0 : QuotBySeminorm (E := space base) p)
  simp

noncomputable def banachEquivL2 (hbase : ∀ n, (1 : ℝ) ≤ base n) (k : ℕ) :
    BanachOfSeminorm (E := space base) (seminorm (base := base) k) ≃ₗᵢ[ℝ] H := by
  let E : Type := QuotBySeminorm (E := space base) (seminorm (base := base) k)
  let T : E →ₗ[ℝ] H := toL2Quotₗ (base := base) k
  let F : Submodule ℝ H := LinearMap.range T
  have hTnorm : ∀ x : E, ‖T x‖ = ‖x‖ := fun x => by
    simpa [T] using (norm_toL2Quotₗ (base := base) (k := k) x)
  have hTinj : Function.Injective T := by
    intro x y hxy
    have : T (x - y) = 0 := by simp [map_sub, hxy]
    have h0 : ‖T (x - y)‖ = 0 := by
      simpa using congrArg (fun z : H => ‖z‖) this
    have hnorm0 : ‖x - y‖ = 0 := by
      calc
        ‖x - y‖ = ‖T (x - y)‖ := (hTnorm (x - y)).symm
        _ = 0 := h0
    simpa using sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  let f : E ≃ₗ[ℝ] F := LinearEquiv.ofInjective T hTinj
  let e₁ : E →ₗ[ℝ] BanachOfSeminorm (E := space base) (seminorm (base := base) k) :=
    (BanachOfSeminorm.coeCLM (E := space base) (seminorm (base := base) k)).toLinearMap
  let e₂ : F →ₗ[ℝ] H := (Submodule.subtype F)
  have h_dense₁ : DenseRange e₁ := by
    simpa [e₁] using (BanachOfSeminorm.denseRange_coeCLM (E := space base) (p := seminorm (base := base) k))
  have h_dense₂ : DenseRange e₂ := by
    have hT_dense : DenseRange T := by
      simpa [T] using denseRange_toL2Quotₗ (base := base) hbase (k := k)
    intro y
    have : y ∈ closure (Set.range T) := hT_dense y
    have hrange : Set.range e₂ = Set.range T := by
      ext z
      constructor
      · rintro ⟨u, rfl⟩
        simp [e₂]
      · rintro ⟨x, rfl⟩
        exact ⟨⟨T x, ⟨x, rfl⟩⟩, rfl⟩
    simpa [hrange] using this
  have h_norm : ∀ x : E, ‖e₂ (f x)‖ = ‖e₁ x‖ := by
    intro x
    have hleft : ‖e₂ (f x)‖ = ‖T x‖ := rfl
    have hright : ‖e₁ x‖ = ‖x‖ := by
      simp [e₁, BanachOfSeminorm.coeCLM]
    simp [hleft, hright, hTnorm x]
  exact (f.extendOfIsometry (σ₁₂ := RingHom.id ℝ) e₁ e₂ h_dense₁ h_dense₂ h_norm)

@[simp]
lemma banachEquivL2_apply_coe (hbase : ∀ n, (1 : ℝ) ≤ base n) (k : ℕ)
    (x : QuotBySeminorm (E := space base) (seminorm (base := base) k)) :
    banachEquivL2 (base := base) hbase k
        (BanachOfSeminorm.coeCLM (E := space base) (seminorm (base := base) k) x) =
      toL2Quotₗ (base := base) k x := by
  change banachEquivL2 (base := base) hbase k
        ((↑(BanachOfSeminorm.coeCLM (E := space base) (seminorm (base := base) k)) :
            QuotBySeminorm (E := space base) (seminorm (base := base) k) →ₗ[ℝ]
              BanachOfSeminorm (E := space base) (seminorm (base := base) k)) x)
      = toL2Quotₗ (base := base) k x
  simp (config := { zeta := true }) [banachEquivL2]
  have hx :
      (BanachOfSeminorm.coeCLM (E := space base) (seminorm (base := base) k) x) =
        ((↑(BanachOfSeminorm.coeCLM (E := space base) (seminorm (base := base) k)) :
            QuotBySeminorm (E := space base) (seminorm (base := base) k) →ₗ[ℝ]
              BanachOfSeminorm (E := space base) (seminorm (base := base) k)) x) := rfl
  rw [hx]
  rw [LinearEquiv.extendOfIsometry_eq]
  rfl

/-! ### Nuclearity of the local inclusions -/

-- A key computation: under weights, the inclusion from level `k+2` to level `k` is diagonal.
lemma diagPowInvCLM_two_toL2 (hbase : ∀ n, (1 : ℝ) ≤ base n) (k : ℕ) (x : space base) :
    diagPowInvCLM (base := base) hbase 2 (toL2ₗ (base := base) (k + 2) x) =
      toL2ₗ (base := base) k x := by
  ext n
  have hn1 : (base n) ≠ 0 := by
    have : (0 : ℝ) < base n := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hbase n)
    exact this.ne'
  have hne2 : weight base 2 n ≠ 0 := by
    simpa [weight] using (pow_ne_zero 2 hn1)
  have hw : weight base (k + 2) n = weight base k n * weight base 2 n := by
    dsimp [weight]
    exact pow_add (base n) k 2
  have hcoef : (weight base 2 n)⁻¹ * weight base (k + 2) n = weight base k n := by
    rw [hw]
    calc
      (weight base 2 n)⁻¹ * (weight base k n * weight base 2 n)
          = ((weight base 2 n)⁻¹ * weight base k n) * weight base 2 n := by
              rw [← mul_assoc]
      _ = (weight base k n * (weight base 2 n)⁻¹) * weight base 2 n := by
            simp [mul_comm]
      _ = weight base k n * (weight base 2 n)⁻¹ * weight base 2 n := by
            rw [mul_assoc]
      _ = weight base k n := by
            simpa [mul_assoc] using
              (inv_mul_cancel_right₀ (b := weight base 2 n) hne2 (a := weight base k n))
  have : (weight base 2 n)⁻¹ * (weight base (k + 2) n * x.1 n) = weight base k n * x.1 n := by
    rw [← mul_assoc (weight base 2 n)⁻¹ (weight base (k + 2) n) (x.1 n)]
    rw [hcoef]
  simpa [diagPowInvCLM_apply, toL2ₗ_apply, sigma, mul_assoc] using this

theorem isNuclearMap_inclCLM_succ_succ (hbase : ∀ n, (1 : ℝ) ≤ base n)
    (hsum : Summable (fun n : ℕ => ((base n) ^ 2)⁻¹)) (k : ℕ) :
    IsNuclearMap
      (BanachOfSeminorm.inclCLM (E := space base)
        (p := seminorm (base := base) (k + 2))
        (q := seminorm (base := base) k)
        (by
          simpa using
            (seminorm_mono (base := base) hbase (a := k) (b := k + 2) (Nat.le_add_right k 2)))) := by
  let E₀ := BanachOfSeminorm (E := space base) (seminorm (base := base) (k + 2))
  let E₁ := BanachOfSeminorm (E := space base) (seminorm (base := base) k)
  let incl : E₀ →L[ℝ] E₁ :=
    BanachOfSeminorm.inclCLM (E := space base)
      (p := seminorm (base := base) (k + 2)) (q := seminorm (base := base) k)
      (by
        simpa using
          (seminorm_mono (base := base) hbase (a := k) (b := k + 2) (Nat.le_add_right k 2)))
  let iso₀ : E₀ ≃ₗᵢ[ℝ] H := banachEquivL2 (base := base) hbase (k + 2)
  let iso₁ : E₁ ≃ₗᵢ[ℝ] H := banachEquivL2 (base := base) hbase k
  let iso₀L : E₀ →L[ℝ] H := iso₀.toContinuousLinearEquiv.toContinuousLinearMap
  let iso₁L : E₁ →L[ℝ] H := iso₁.toContinuousLinearEquiv.toContinuousLinearMap
  let iso₁Linv : H →L[ℝ] E₁ := iso₁.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have h_conj : (iso₁L.comp incl) = (diagPowInvCLM (base := base) hbase 2).comp iso₀L := by
    apply ContinuousLinearMap.coeFn_injective
    have hd : DenseRange (BanachOfSeminorm.coeCLM (E := space base) (seminorm (base := base) (k + 2))) :=
      BanachOfSeminorm.denseRange_coeCLM (E := space base) (p := seminorm (base := base) (k + 2))
    have hs : Dense (Set.range (BanachOfSeminorm.coeCLM (E := space base) (seminorm (base := base) (k + 2)))) := by
      refine dense_iff_closure_eq.2 ?_
      exact (denseRange_iff_closure_range).1 hd
    refine Continuous.ext_on hs (by fun_prop) (by fun_prop) ?_
    rintro _ ⟨xq, rfl⟩
    refine Submodule.Quotient.induction_on
      (p := seminormKer (E := space base) (p := seminorm (base := base) (k + 2))) xq ?_
    intro x
    simp [incl, iso₀, iso₁, iso₀L, iso₁L]
    rw [BanachOfSeminorm.inclCLM_coeCLM]
    simp [QuotBySeminorm.inclCLM_mk]
    rw [banachEquivL2_apply_coe (base := base) (hbase := hbase) (k := k) (x := Submodule.Quotient.mk x)]
    rw [banachEquivL2_apply_coe (base := base) (hbase := hbase) (k := k + 2) (x := Submodule.Quotient.mk x)]
    simp [toL2Quotₗ_mk]
    simpa using (diagPowInvCLM_two_toL2 (base := base) hbase (k := k) (x := x)).symm
  have h_incl : incl = iso₁Linv.comp ((diagPowInvCLM (base := base) hbase 2).comp iso₀L) := by
    calc
      incl = iso₁Linv.comp (iso₁L.comp incl) := by
        ext y
        simp [iso₁Linv, iso₁L, ContinuousLinearMap.comp_apply]
      _ = iso₁Linv.comp ((diagPowInvCLM (base := base) hbase 2).comp iso₀L) := by
        simpa [ContinuousLinearMap.comp_assoc] using congrArg (fun T => iso₁Linv.comp T) h_conj
  have hsum_sigma : Summable (fun n : ℕ => ‖sigma (base := base) 2 n‖) := by
    have hpos : ∀ n, 0 < base n := fun n =>
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hbase n)
    have hnorm : (fun n : ℕ => ‖sigma (base := base) 2 n‖) = fun n : ℕ => ((base n) ^ 2)⁻¹ := by
      funext n
      have hposw : 0 < weight base 2 n := by simpa [weight] using pow_pos (hpos n) 2
      have hposInv : 0 < (weight base 2 n)⁻¹ := inv_pos_of_pos hposw
      simp [Real.norm_eq_abs, sigma, weight]
    rw [hnorm]
    exact hsum
  have h_diag : IsNuclearMap (diagPowInvCLM (base := base) hbase 2) :=
    isNuclearMap_diagPowInvCLM_of_summable (base := base) hbase 2 hsum_sigma
  have h_diag_pre : IsNuclearMap ((diagPowInvCLM (base := base) hbase 2).comp iso₀L) :=
    IsNuclearMap.comp_right (T := diagPowInvCLM (base := base) hbase 2) h_diag iso₀L
  have h_all : IsNuclearMap (iso₁Linv.comp ((diagPowInvCLM (base := base) hbase 2).comp iso₀L)) :=
    IsNuclearMap.comp_left (T := (diagPowInvCLM (base := base) hbase 2).comp iso₀L) h_diag_pre iso₁Linv
  simpa [incl, ← h_incl] using h_all

/-! ### The promised `NuclearSpaceStd` instance -/

theorem nuclearSpaceStd_space (hbase : ∀ n, (1 : ℝ) ≤ base n)
    (hsum : Summable (fun n : ℕ => ((base n) ^ 2)⁻¹)) :
    NuclearSpaceStd (space base) := by
  refine ⟨?_⟩
  refine ⟨(fun k : ℕ => seminorm (base := base) k),
    seminorm_mono (base := base) hbase, withSeminorms (base := base), ?_⟩
  intro k
  refine ⟨k + 2, Nat.lt_add_of_pos_right (n := k) (k := 2) (h := by decide), ?_⟩
  simpa using (isNuclearMap_inclCLM_succ_succ (base := base) hbase hsum (k := k))

noncomputable instance (hbase : ∀ n, (1 : ℝ) ≤ base n)
    (hsum : Summable (fun n : ℕ => ((base n) ^ 2)⁻¹)) :
    NuclearSpaceStd (space base) :=
  nuclearSpaceStd_space (base := base) hbase hsum

end Space

end RapidDecaySeqBase

end
end OSforGFF
