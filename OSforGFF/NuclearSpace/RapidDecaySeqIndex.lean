/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.InnerProductSpace.l2Space

import OSforGFF.NuclearSpace.Defs
import OSforGFF.NuclearSpace.Std

/-!
# Rapidly decreasing sequences on a general index type (weighted `ℓ²`)

This file generalizes `OSforGFF.NuclearSpace.RapidDecaySeqBase` from sequences indexed by `ℕ`
to functions indexed by an arbitrary type `ι`.

We only develop the *index-generic* analytic API needed downstream:

- the weighted rapid-decay submodule `space base`,
- the diagonal map on `ℓ²(ι,ℝ)` given by multiplication with `(base i)^{-s}`,
- nuclearity of this diagonal map from an `ℓ¹` summability hypothesis.

Downstream, we will instantiate `ι := (Fin d → ℕ)` and `base` a multi-index weight.
-/

open scoped BigOperators NNReal ENNReal

namespace OSforGFF

noncomputable section

namespace RapidDecaySeqIndex

variable {ι : Type*} (base : ι → ℝ)

local notation "H" => ℓ²(ι, ℝ)

/-- The weights \(w_k(i) = (base\ i)^k\). -/
def weight (k : ℕ) (i : ι) : ℝ := (base i) ^ k

/-- Pointwise weighting of a function by `weight`. -/
def weightFun (k : ℕ) (f : ι → ℝ) : ι → ℝ := fun i => weight base k i * f i

@[simp]
lemma weight_zero (i : ι) : weight base 0 i = 1 := by
  simp [weight]

@[simp]
lemma weight_succ (k : ℕ) (i : ι) :
    weight base (k + 1) i = weight base k i * base i := by
  simp [weight, pow_succ]

/-- The submodule of functions whose weighted versions are in `ℓ²` for every weight. -/
def space : Submodule ℝ (ι → ℝ) where
  carrier := { f | ∀ k : ℕ, Memℓp (weightFun base k f) (2 : ℝ≥0∞) }
  zero_mem' := by
    intro k
    have h0 : weightFun base k (0 : ι → ℝ) = 0 := by
      funext i
      simp [weightFun]
    simpa [h0] using (zero_memℓp (E := fun _ : ι => ℝ) (p := (2 : ℝ≥0∞)))
  add_mem' := by
    intro f g hf hg k
    have hfg : weightFun base k (f + g) = weightFun base k f + weightFun base k g := by
      funext i
      simp [weightFun, mul_add]
    simpa [hfg] using (hf k).add (hg k)
  smul_mem' := by
    intro c f hf k
    have hsmul : weightFun base k (c • f) = c • weightFun base k f := by
      funext i
      simp [weightFun, mul_assoc, mul_comm]
    simpa [hsmul] using (hf k).const_smul c

/-! We use `space base` as a **type** via the coercion `Submodule → Sort`. -/

namespace Space

variable (k : ℕ)

/-- The canonical map to `ℓ²`: send a rapidly decreasing function to its `k`-weighted version. -/
noncomputable def toL2ₗ : (space base) →ₗ[ℝ] H where
  toFun x := ⟨weightFun base k x.1, x.2 k⟩
  map_add' x y := by
    ext i
    simp [weightFun, mul_add]
  map_smul' c x := by
    ext i
    simp [weightFun, mul_left_comm]

@[simp]
lemma toL2ₗ_apply (x : space base) (i : ι) :
    (toL2ₗ (base := base) k x : ι → ℝ) i = weight base k i * x.1 i := rfl

/-- The weighted `ℓ²` seminorms generating the Fréchet topology. -/
noncomputable def seminorm : Seminorm ℝ (space base) :=
  (normSeminorm ℝ H).comp (toL2ₗ (base := base) k)

@[simp]
lemma seminorm_apply (x : space base) :
    seminorm (base := base) k x = ‖toL2ₗ (base := base) k x‖ := rfl

variable {base}

theorem seminorm_mono (hbase : ∀ i, (1 : ℝ) ≤ base i) :
    Monotone (fun k : ℕ => seminorm (base := base) k) := by
  intro a b hab x
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  let A : H := toL2ₗ (base := base) a x
  let B : H := toL2ₗ (base := base) b x
  have hAB : ‖A‖ ≤ ‖B‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := ‖B‖) (by positivity) ?_
    intro s
    have hpoint :
        ∀ i : ι, ‖A i‖ ^ ((2 : ℝ≥0∞).toReal) ≤ ‖B i‖ ^ ((2 : ℝ≥0∞).toReal) := by
      intro i
      have hle_w : weight base a i ≤ weight base b i := by
        simpa [weight] using (pow_le_pow_right₀ (hbase i) hab)
      have hi : 0 ≤ weight base a i := by
        have : 0 ≤ base i := (zero_le_one.trans (hbase i))
        simpa [weight] using pow_nonneg this a
      have hi' : 0 ≤ weight base b i := by
        have : 0 ≤ base i := (zero_le_one.trans (hbase i))
        simpa [weight] using pow_nonneg this b
      have habs : ‖(weight base a i * x.1 i)‖ ≤ ‖(weight base b i * x.1 i)‖ := by
        simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hi, abs_of_nonneg hi'] using
          mul_le_mul_of_nonneg_right hle_w (abs_nonneg (x.1 i))
      have :
          (‖weight base a i * x.1 i‖) ^ ((2 : ℝ≥0∞).toReal)
            ≤ (‖weight base b i * x.1 i‖) ^ ((2 : ℝ≥0∞).toReal) := by
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
      (p := fun k : ℕ => seminorm (base := base) k)).topology

theorem withSeminorms : WithSeminorms (fun k : ℕ => seminorm (base := base) k) := by
  exact ⟨rfl⟩

/-! ## A diagonal nuclear operator on `ℓ²` -/

/-- Coefficients \(\sigma_s(i) = (base\ i)^{-s}\). -/
def sigma (s : ℕ) (i : ι) : ℝ := (weight base s i)⁻¹

@[simp]
lemma sigma_apply (s : ℕ) (i : ι) : sigma (base := base) s i = (weight base s i)⁻¹ := rfl

lemma abs_sigma_le_one (hbase : ∀ i, (1 : ℝ) ≤ base i) (s : ℕ) (i : ι) :
    |sigma (base := base) s i| ≤ 1 := by
  have hpos : 0 < weight base s i := by
    have : 0 < base i := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hbase i)
    simpa [weight] using (pow_pos this s)
  have hone : (1 : ℝ) ≤ weight base s i := by
    simpa [weight] using (one_le_pow₀ (a := base i) (hbase i) (n := s))
  have : (weight base s i)⁻¹ ≤ 1 := by
    simpa [one_div] using (inv_le_one_of_one_le₀ hone)
  simpa [sigma, abs_of_pos (inv_pos_of_pos hpos)] using this

variable [DecidableEq ι]

/-- The diagonal linear map on `ℓ²` given by multiplying coordinates by `sigma s`. -/
noncomputable def diagPowInvₗ (hbase : ∀ i, (1 : ℝ) ≤ base i) (s : ℕ) : H →ₗ[ℝ] H where
  toFun x :=
    ⟨fun i => sigma (base := base) s i * x i, by
      have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
      have hx : Summable (fun i : ι => ‖x i‖ ^ ((2 : ℝ≥0∞).toReal)) :=
        (lp.memℓp x).summable hp
      have hnonneg : ∀ i : ι, 0 ≤ ‖sigma (base := base) s i * x i‖ ^ ((2 : ℝ≥0∞).toReal) := by
        intro i; positivity
      have hle : ∀ i : ι,
          ‖sigma (base := base) s i * x i‖ ^ ((2 : ℝ≥0∞).toReal) ≤ ‖x i‖ ^ ((2 : ℝ≥0∞).toReal) := by
        intro i
        have : ‖sigma (base := base) s i * x i‖ ≤ ‖x i‖ := by
          have hs : ‖sigma (base := base) s i‖ ≤ 1 := by
            simpa [Real.norm_eq_abs] using abs_sigma_le_one (base := base) hbase s i
          calc
            ‖sigma (base := base) s i * x i‖ = ‖sigma (base := base) s i‖ * ‖x i‖ := by
              simp [norm_mul]
            _ ≤ 1 * ‖x i‖ := by gcongr
            _ = ‖x i‖ := by simp
        exact Real.rpow_le_rpow (norm_nonneg _) this (by norm_num)
      refine memℓp_gen (p := (2 : ℝ≥0∞)) ?_
      exact Summable.of_nonneg_of_le hnonneg hle hx⟩
  map_add' x y := by
    ext i
    change sigma (base := base) s i * (x i + y i) =
      sigma (base := base) s i * x i + sigma (base := base) s i * y i
    simp [mul_add]
  map_smul' c x := by
    ext i
    simp [mul_left_comm]

omit [DecidableEq ι] in
@[simp]
lemma diagPowInvₗ_apply (hbase : ∀ i, (1 : ℝ) ≤ base i) (s : ℕ) (x : H) (i : ι) :
  (diagPowInvₗ (base := base) hbase s x : ι → ℝ) i = sigma (base := base) s i * x i := rfl

/-- The diagonal continuous linear map on `ℓ²` given by multiplying coordinates by `sigma s`. -/
noncomputable def diagPowInvCLM (hbase : ∀ i, (1 : ℝ) ≤ base i) (s : ℕ) : H →L[ℝ] H := by
  refine (diagPowInvₗ (base := base) hbase s).mkContinuous 1 ?_
  intro x
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  let y : H := diagPowInvₗ (base := base) hbase s x
  have hy : ‖y‖ ≤ ‖x‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := ‖x‖) (by positivity) ?_
    intro t
    have hle_term : ∀ i : ι, ‖y i‖ ^ ((2 : ℝ≥0∞).toReal) ≤ ‖x i‖ ^ ((2 : ℝ≥0∞).toReal) := by
      intro i
      have : ‖y i‖ ≤ ‖x i‖ := by
        have hs' : ‖sigma (base := base) s i‖ ≤ 1 := by
          simpa [Real.norm_eq_abs] using abs_sigma_le_one (base := base) hbase s i
        calc
          ‖y i‖ = ‖sigma (base := base) s i * x i‖ := by
              simp [y, diagPowInvₗ_apply]
          _ = ‖sigma (base := base) s i‖ * ‖x i‖ := by simp [norm_mul]
          _ ≤ 1 * ‖x i‖ := by gcongr
          _ = ‖x i‖ := by simp
      exact Real.rpow_le_rpow (norm_nonneg _) this (by norm_num)
    calc
      ∑ i ∈ t, ‖y i‖ ^ ((2 : ℝ≥0∞).toReal)
          ≤ ∑ i ∈ t, ‖x i‖ ^ ((2 : ℝ≥0∞).toReal) := by
              exact Finset.sum_le_sum fun i hi => hle_term i
      _ ≤ ‖x‖ ^ ((2 : ℝ≥0∞).toReal) := by
            simpa using (lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) hp x t)
  simpa [y] using (hy.trans_eq (by simp))

omit [DecidableEq ι] in
@[simp]
lemma diagPowInvCLM_apply (hbase : ∀ i, (1 : ℝ) ≤ base i) (s : ℕ) (x : H) (i : ι) :
  (diagPowInvCLM (base := base) hbase s x : ι → ℝ) i = sigma (base := base) s i * x i := rfl

/-! ### Nuclearity of the diagonal map from an `ℓ¹` hypothesis -/
theorem isNuclearMap_diagPowInvCLM_of_summable [Encodable ι]
    (hbase : ∀ i, (1 : ℝ) ≤ base i) (s : ℕ)
    (hsum : Summable (fun i : ι => ‖sigma (base := base) s i‖)) :
    IsNuclearMap (diagPowInvCLM (base := base) hbase s) := by
  classical
  let enc : ι → ℕ := Encodable.encode
  have henc : Function.Injective enc := by
    intro a b hab
    have h := congrArg (fun n : ℕ => (Encodable.decode n : Option ι)) hab
    simpa [enc, Encodable.encodek] using h
  haveI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let e : ι → H := fun i => lp.single (E := fun _ : ι => ℝ) 2 i (1 : ℝ)
  let φ₀ : ι → (H →L[ℝ] ℝ) := fun i => innerSL ℝ (e i)
  let y₀ : ι → H := fun i => (sigma (base := base) s i) • e i
  -- Extend by `0` outside the range of `enc`.
  let φ : ℕ → (H →L[ℝ] ℝ) := Function.extend enc φ₀ 0
  let y : ℕ → H := Function.extend enc y₀ 0
  refine ⟨φ, y, ?_, ?_⟩
  · have hφ₀ : ∀ i, ‖φ₀ i‖ = 1 := by
      intro i
      have he : ‖e i‖ = 1 := by simp [e]
      calc
        ‖φ₀ i‖ = ‖e i‖ := by simp [φ₀]
        _ = 1 := he
    have hy₀ : ∀ i, ‖y₀ i‖ = ‖sigma (base := base) s i‖ := by
      intro i
      have : ‖e i‖ = 1 := by simp [e]
      simp [y₀, this, norm_smul]
    have hnorm :
        (fun n : ℕ => ‖φ n‖ * ‖y n‖)
          =
        Function.extend enc (fun i : ι => ‖sigma (base := base) s i‖) 0 := by
      funext n
      by_cases h : ∃ i, enc i = n
      · simp [φ, y, Function.extend, h, hφ₀, hy₀]
      · simp [φ, y, Function.extend, h]
    have hsum' :
        Summable (Function.extend enc (fun i : ι => ‖sigma (base := base) s i‖) 0) := by
      simpa using ((summable_extend_zero (g := enc) (f := fun i : ι => ‖sigma (base := base) s i‖) henc).2 hsum)
    rw [hnorm]
    exact hsum'
  · intro x
    have hx :
        HasSum (fun i : ι => lp.single 2 i ((diagPowInvCLM (base := base) hbase s x) i))
          (diagPowInvCLM (base := base) hbase s x) :=
      lp.hasSum_single (E := fun _ : ι => ℝ) (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top
        (diagPowInvCLM (base := base) hbase s x)
    have hterm0 :
        ∀ i : ι, lp.single 2 i ((diagPowInvCLM (base := base) hbase s x) i) = (φ₀ i x) • y₀ i := by
      intro i
      have hφx : φ₀ i x = x i := by
        simpa [φ₀, e, innerSL_apply_apply] using
          (lp.inner_single_left (𝕜 := ℝ) (ι := ι) (G := fun _ : ι => ℝ) i (1 : ℝ) x)
      have hs' :
          lp.single (E := fun _ : ι => ℝ) (2 : ℝ≥0∞) i ((weight base s i)⁻¹ * x i) =
            ((weight base s i)⁻¹ * x i) • lp.single (E := fun _ : ι => ℝ) (2 : ℝ≥0∞) i (1 : ℝ) := by
        simpa using
          (lp.single_smul (E := fun _ : ι => ℝ) (p := (2 : ℝ≥0∞)) i ((weight base s i)⁻¹ * x i) (1 : ℝ))
      simp [y₀, e, diagPowInvCLM_apply, hφx, hs', sigma, smul_smul, mul_comm]
    have hx0 :
        HasSum (fun i : ι => (φ₀ i x) • y₀ i) (diagPowInvCLM (base := base) hbase s x) :=
      HasSum.congr_fun hx (fun i => (hterm0 i).symm)
    have hxNat :
        HasSum (Function.extend enc (fun i : ι => (φ₀ i x) • y₀ i) 0)
          (diagPowInvCLM (base := base) hbase s x) := by
      simpa using ((hasSum_extend_zero (g := enc) (f := fun i : ι => (φ₀ i x) • y₀ i)
        (a := diagPowInvCLM (base := base) hbase s x) henc).2 hx0)
    have hpoint :
        (fun n : ℕ => (φ n x) • y n)
          =
        (Function.extend enc (fun i : ι => (φ₀ i x) • y₀ i) 0) := by
      funext n
      by_cases h : ∃ i, enc i = n
      · simp [φ, y, Function.extend, h]
      · simp [φ, y, Function.extend, h]
    have hxNat' :
        HasSum (fun n : ℕ => (φ n x) • y n) (diagPowInvCLM (base := base) hbase s x) := by
      simpa [hpoint] using hxNat
    exact hxNat'.tsum_eq.symm

/-!
## `space base` is a standard nuclear Fréchet space (under a summability hypothesis)

We reuse the same strategy as in `OSforGFF.NuclearSpace.RapidDecaySeqBase`:
- identify the local Banach spaces with `ℓ²` via the weighted maps;
- show the local inclusion from level `k+2` to level `k` is conjugate to a diagonal operator;
- conclude nuclearity from `∑ (base i)⁻² < ∞`.
-/

open scoped Topology

-- Force quotient topology to be the norm-induced one (see `RapidDecaySeq.lean` for discussion).
local instance (priority := 1001) (k : ℕ) :
    TopologicalSpace (QuotBySeminorm (E := space base) (seminorm (base := base) k)) :=
  (PseudoMetricSpace.toUniformSpace.toTopologicalSpace :
    TopologicalSpace (QuotBySeminorm (E := space base) (seminorm (base := base) k)))

noncomputable def toL2Quotₗ (k : ℕ) :
    QuotBySeminorm (E := space base) (seminorm (base := base) k) →ₗ[ℝ] H :=
  (seminormKer (E := space base) (p := seminorm (base := base) k)).liftQ
    (toL2ₗ (base := base) k) (by
      intro x hx
      have hx0 : seminorm (base := base) k x = 0 := hx
      have : ‖toL2ₗ (base := base) k x‖ = 0 := by
        simpa [seminorm_apply] using hx0
      exact (norm_eq_zero.mp this))

omit [DecidableEq ι] in
@[simp]
lemma toL2Quotₗ_mk (k : ℕ) (x : space base) :
    toL2Quotₗ (base := base) k
        (Submodule.Quotient.mk
          (p := seminormKer (E := space base) (p := seminorm (base := base) k)) x) =
      toL2ₗ (base := base) k x := by
  simp [toL2Quotₗ]

omit [DecidableEq ι] in
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
        (Submodule.Quotient.mk
          (p := seminormKer (E := space base) (p := seminorm (base := base) k)) y)‖
        = ‖toL2ₗ (base := base) k y‖ := by simp [toL2Quotₗ_mk]
    _ = seminorm (base := base) k y := by simp [seminorm_apply]
    _ = ‖(Submodule.Quotient.mk
            (p := seminormKer (E := space base) (p := seminorm (base := base) k)) y :
          QuotBySeminorm (E := space base) (seminorm (base := base) k))‖ := by
        simp [hy_norm]

lemma denseRange_toL2ₗ (hbase : ∀ i, (1 : ℝ) ≤ base i) (k : ℕ) :
    DenseRange (toL2ₗ (base := base) k) := by
  classical
  intro y
  haveI : Fact ((1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hy_hasSum :
      HasSum (fun i : ι => lp.single (E := fun _ : ι => ℝ) (2 : ℝ≥0∞) i (y i)) y :=
    lp.hasSum_single (E := fun _ : ι => ℝ) (p := (2 : ℝ≥0∞)) ENNReal.ofNat_ne_top y
  have h_mem_range :
      ∀ s : Finset ι,
        (∑ i ∈ s, lp.single (E := fun _ : ι => ℝ) (2 : ℝ≥0∞) i (y i))
          ∈ Set.range (toL2ₗ (base := base) k) := by
    intro s
    let f : ι → ℝ := fun i => if i ∈ s then (weight base k i)⁻¹ * y i else 0
    have hf : ∀ j : ℕ, Memℓp (weightFun base j f) (2 : ℝ≥0∞) := by
      intro j
      have hsum :
          Summable (fun i : ι => ‖(weightFun base j f) i‖ ^ ((2 : ℝ≥0∞).toReal)) := by
        refine summable_of_finite_support <| s.finite_toSet.subset ?_
        intro i hi
        have : i ∈ s := by
          by_contra his
          have hf0 : f i = 0 := by simp [f, his]
          have : (weightFun base j f) i = 0 := by simp [weightFun, hf0]
          have : (‖(weightFun base j f) i‖ ^ ((2 : ℝ≥0∞).toReal)) = 0 := by simp [this]
          exact hi (by simpa using this)
        exact this
      exact memℓp_gen (p := (2 : ℝ≥0∞)) hsum
    let xs : space base := ⟨f, hf⟩
    refine ⟨xs, ?_⟩
    ext i
    by_cases hi : i ∈ s
    · have hi0 : base i ≠ 0 := by
        have : (0 : ℝ) < base i := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hbase i)
        exact this.ne'
      have hne : weight base k i ≠ 0 := by
        simpa [weight] using (pow_ne_zero k hi0)
      have : (toL2ₗ (base := base) k xs : ι → ℝ) i = y i := by
        calc
          (toL2ₗ (base := base) k xs : ι → ℝ) i =
              weight base k i * ((weight base k i)⁻¹ * y i) := by
                simp [toL2ₗ_apply, xs, f, hi]
          _ = y i := by
            rw [← mul_assoc (weight base k i) (weight base k i)⁻¹ (y i)]
            simp [hne]
      simp [this, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single, hi]
    · have hi' : i ∉ s := hi
      have : (toL2ₗ (base := base) k xs : ι → ℝ) i = 0 := by
        simp [toL2ₗ_apply, xs, f, hi']
      simp [this, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single, hi']
  refine mem_closure_of_tendsto hy_hasSum (Filter.Eventually.of_forall h_mem_range)

lemma denseRange_toL2Quotₗ (hbase : ∀ i, (1 : ℝ) ≤ base i) (k : ℕ) :
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

omit [DecidableEq ι] in
lemma norm_coe_banachOfSeminorm
    (p : Seminorm ℝ (space base)) (x : QuotBySeminorm (E := space base) p) :
    ‖(x : BanachOfSeminorm (E := space base) p)‖ = ‖x‖ := by
  have hIso :
      Isometry ((↑) :
        QuotBySeminorm (E := space base) p → BanachOfSeminorm (E := space base) p) :=
    UniformSpace.Completion.coe_isometry
  have _ := hIso.dist_eq x (0 : QuotBySeminorm (E := space base) p)
  simp

noncomputable def banachEquivL2 (hbase : ∀ i, (1 : ℝ) ≤ base i) (k : ℕ) :
    BanachOfSeminorm (E := space base) (seminorm (base := base) k) ≃ₗᵢ[ℝ] H := by
  let E : Type _ := QuotBySeminorm (E := space base) (seminorm (base := base) k)
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
    simpa [e₁] using
      (BanachOfSeminorm.denseRange_coeCLM (E := space base) (p := seminorm (base := base) k))
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
lemma banachEquivL2_apply_coe (hbase : ∀ i, (1 : ℝ) ≤ base i) (k : ℕ)
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

omit [DecidableEq ι] in
-- A key computation: under weights, the inclusion from level `k+2` to level `k` is diagonal.
lemma diagPowInvCLM_two_toL2 (hbase : ∀ i, (1 : ℝ) ≤ base i) (k : ℕ) (x : space base) :
    diagPowInvCLM (base := base) hbase 2 (toL2ₗ (base := base) (k + 2) x) =
      toL2ₗ (base := base) k x := by
  ext i
  have hi1 : (base i) ≠ 0 := by
    have : (0 : ℝ) < base i := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hbase i)
    exact this.ne'
  have hne2 : weight base 2 i ≠ 0 := by
    simpa [weight] using (pow_ne_zero 2 hi1)
  have hw : weight base (k + 2) i = weight base k i * weight base 2 i := by
    dsimp [weight]
    exact pow_add (base i) k 2
  have hcoef : (weight base 2 i)⁻¹ * weight base (k + 2) i = weight base k i := by
    rw [hw]
    calc
      (weight base 2 i)⁻¹ * (weight base k i * weight base 2 i)
          = ((weight base 2 i)⁻¹ * weight base k i) * weight base 2 i := by
              rw [← mul_assoc]
      _ = (weight base k i * (weight base 2 i)⁻¹) * weight base 2 i := by
            simp [mul_comm]
      _ = weight base k i * (weight base 2 i)⁻¹ * weight base 2 i := by
            rw [mul_assoc]
      _ = weight base k i := by
            simpa [mul_assoc] using
              (inv_mul_cancel_right₀ (b := weight base 2 i) hne2 (a := weight base k i))
  have : (weight base 2 i)⁻¹ * (weight base (k + 2) i * x.1 i) = weight base k i * x.1 i := by
    rw [← mul_assoc (weight base 2 i)⁻¹ (weight base (k + 2) i) (x.1 i)]
    rw [hcoef]
  simpa [diagPowInvCLM_apply, toL2ₗ_apply, sigma, mul_assoc] using this

theorem isNuclearMap_inclCLM_succ_succ [Encodable ι]
    (hbase : ∀ i, (1 : ℝ) ≤ base i) (hsum : Summable (fun i : ι => ((base i) ^ 2)⁻¹)) (k : ℕ) :
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
    have hd :
        DenseRange (BanachOfSeminorm.coeCLM (E := space base) (seminorm (base := base) (k + 2))) :=
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
    rw [banachEquivL2_apply_coe (base := base) (hbase := hbase) (k := k)
      (x := Submodule.Quotient.mk x)]
    rw [banachEquivL2_apply_coe (base := base) (hbase := hbase) (k := k + 2)
      (x := Submodule.Quotient.mk x)]
    simp [toL2Quotₗ_mk]
    simpa using (diagPowInvCLM_two_toL2 (base := base) hbase (k := k) (x := x)).symm
  have h_incl : incl = iso₁Linv.comp ((diagPowInvCLM (base := base) hbase 2).comp iso₀L) := by
    calc
      incl = iso₁Linv.comp (iso₁L.comp incl) := by
        ext y
        simp [iso₁Linv, iso₁L, ContinuousLinearMap.comp_apply]
      _ = iso₁Linv.comp ((diagPowInvCLM (base := base) hbase 2).comp iso₀L) := by
        simpa [ContinuousLinearMap.comp_assoc] using congrArg (fun T => iso₁Linv.comp T) h_conj
  have hsum_sigma : Summable (fun i : ι => ‖sigma (base := base) 2 i‖) := by
    have hpos : ∀ i, 0 < base i := fun i =>
      lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hbase i)
    have hnorm : (fun i : ι => ‖sigma (base := base) 2 i‖) = fun i : ι => ((base i) ^ 2)⁻¹ := by
      funext i
      have hposw : 0 < weight base 2 i := by simpa [weight] using pow_pos (hpos i) 2
      have _ : 0 < (weight base 2 i)⁻¹ := inv_pos_of_pos hposw
      simp [Real.norm_eq_abs, sigma, weight]
    rw [hnorm]
    exact hsum
  have h_diag : IsNuclearMap (diagPowInvCLM (base := base) hbase 2) :=
    isNuclearMap_diagPowInvCLM_of_summable (base := base) hbase 2 hsum_sigma
  have h_diag_pre : IsNuclearMap ((diagPowInvCLM (base := base) hbase 2).comp iso₀L) :=
    IsNuclearMap.comp_right (T := diagPowInvCLM (base := base) hbase 2) h_diag iso₀L
  have h_all :
      IsNuclearMap (iso₁Linv.comp ((diagPowInvCLM (base := base) hbase 2).comp iso₀L)) :=
    IsNuclearMap.comp_left (T := (diagPowInvCLM (base := base) hbase 2).comp iso₀L) h_diag_pre iso₁Linv
  simpa [incl, ← h_incl] using h_all

/-! ### The promised `NuclearSpaceStd` instance -/

theorem nuclearSpaceStd_space [Encodable ι]
    (hbase : ∀ i, (1 : ℝ) ≤ base i) (hsum : Summable (fun i : ι => ((base i) ^ 2)⁻¹)) :
    NuclearSpaceStd (space base) := by
  refine ⟨?_⟩
  refine ⟨(fun k : ℕ => seminorm (base := base) k),
    seminorm_mono (base := base) hbase, withSeminorms (base := base), ?_⟩
  intro k
  refine ⟨k + 2, Nat.lt_add_of_pos_right (n := k) (k := 2) (h := by decide), ?_⟩
  simpa using (isNuclearMap_inclCLM_succ_succ (base := base) hbase hsum (k := k))

noncomputable instance [Encodable ι] (hbase : ∀ i, (1 : ℝ) ≤ base i)
    (hsum : Summable (fun i : ι => ((base i) ^ 2)⁻¹)) :
    NuclearSpaceStd (space base) :=
  nuclearSpaceStd_space (base := base) hbase hsum

end Space

end RapidDecaySeqIndex

end

end OSforGFF
