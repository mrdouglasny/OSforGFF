/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic

import OSforGFF.NuclearSpace.RapidDecaySeqIndex

/-!
# Multi-index rapid-decay models on `Fin d → ℕ`

This file replaces the `Nat`-encoding approach of `RapidDecaySeqMulti.lean` by working directly
with canonical multi-indices `α : Fin d → ℕ`.

We define the standard product weight

`base_d α = ∏ i, (α i + 1 : ℝ)`

and prove the summability condition needed for nuclearity:

`Summable (fun α : (Fin d → ℕ) => (base_d α ^ 2)⁻¹)`.

Combined with `OSforGFF.NuclearSpace.RapidDecaySeqIndex`, this yields an axiom-free
`NuclearSpaceStd` instance for the corresponding rapidly decreasing multi-index coefficient space.
-/

open scoped BigOperators

namespace OSforGFF

noncomputable section

namespace RapidDecaySeqMultiIndex

/-! ## The basic 1D summable weight `((n+1)^2)⁻¹` -/

/-- The 1D weight `a n = ((n+1)^2)⁻¹`. -/
def a (n : ℕ) : ℝ := ((n + 1 : ℝ) ^ 2)⁻¹

lemma a_nonneg (n : ℕ) : 0 ≤ a n := by
  have hpos : 0 < ((n + 1 : ℝ) ^ 2) := by
    have : 0 < (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
    positivity
  exact inv_nonneg.2 (le_of_lt hpos)

theorem summable_a : Summable a := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
    exact (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
  have h₁ : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    simpa using ((_root_.summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) 1).2 h)
  simpa [a, Nat.cast_add_one] using h₁

/-! ## Multi-index base and summability -/

/-- The canonical product base on multi-indices `α : Fin d → ℕ`. -/
def base_d (d : ℕ) (α : Fin d → ℕ) : ℝ :=
  ∏ i : Fin d, (α i + 1 : ℝ)

lemma one_le_base_d (d : ℕ) (α : Fin d → ℕ) : (1 : ℝ) ≤ base_d d α := by
  have hfactor : ∀ i : Fin d, (1 : ℝ) ≤ (α i + 1 : ℝ) := by
    intro i; exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
  induction d with
  | zero =>
      simp [base_d]
  | succ d ih =>
      have : base_d (d + 1) α =
          (α ⟨0, Nat.succ_pos d⟩ + 1 : ℝ) *
            base_d d (fun i : Fin d => α i.succ) := by
        simp [base_d, Fin.prod_univ_succ]
      have h0 : (1 : ℝ) ≤ (α ⟨0, Nat.succ_pos d⟩ + 1 : ℝ) := hfactor _
      have htail : (1 : ℝ) ≤ base_d d (fun i : Fin d => α i.succ) := by
        simpa using (ih (α := fun i : Fin d => α i.succ))
      simpa [this] using mul_le_mul h0 htail (by positivity) (by linarith)

lemma base_d_pos (d : ℕ) (α : Fin d → ℕ) : 0 < base_d d α :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_base_d d α)

lemma base_d_ne_zero (d : ℕ) (α : Fin d → ℕ) : base_d d α ≠ 0 :=
  (base_d_pos d α).ne'

theorem summable_inv_sq_base_d : ∀ d : ℕ,
    Summable (fun α : (Fin d → ℕ) => (base_d d α ^ 2)⁻¹)
  | 0 => by
      classical
      haveI : Unique (Fin 0 → ℕ) := by infer_instance
      have hsum :
          HasSum (fun α : (Fin 0 → ℕ) => (base_d 0 α ^ 2)⁻¹)
            ((base_d 0 (default : Fin 0 → ℕ) ^ 2)⁻¹) := by
        exact hasSum_unique (fun α : (Fin 0 → ℕ) => (base_d 0 α ^ 2)⁻¹)
      exact hsum.summable
  | d + 1 => by
      classical
      let b : (Fin d → ℕ) → ℝ := fun β => (base_d d β ^ 2)⁻¹
      have hb : Summable b := by simpa [b] using (summable_inv_sq_base_d d)
      have ha : Summable (fun n : ℕ => a n) := summable_a
      have hab :
          Summable (fun p : ℕ × (Fin d → ℕ) => a p.1 * b p.2) := by
        refine Summable.mul_of_nonneg ha hb ?_ ?_
        · intro n; exact a_nonneg n
        · intro β
          have : 0 ≤ (base_d d β ^ 2) := sq_nonneg (base_d d β)
          exact inv_nonneg.2 this
      let e : (Fin (d + 1) → ℕ) ≃ (ℕ × (Fin d → ℕ)) :=
        (Fin.consEquiv (α := fun _ : Fin (d + 1) => ℕ)).symm
      have hsum₁ : Summable (fun α : (Fin (d + 1) → ℕ) =>
          a (α 0) * b (Fin.tail α)) := by
        have : Summable (fun p : ℕ × (Fin d → ℕ) => a p.1 * b p.2) := hab
        simpa [e] using (e.summable_iff.mpr this)
      have hsummand :
          (fun α : (Fin (d + 1) → ℕ) => (base_d (d + 1) α ^ 2)⁻¹)
            =
          fun α : (Fin (d + 1) → ℕ) => a (α 0) * b (Fin.tail α) := by
        funext α
        have hprod :
            base_d (d + 1) α = (α 0 + 1 : ℝ) * base_d d (Fin.tail α) := by
          simp [base_d, Fin.tail, Fin.prod_univ_succ]
        have : (base_d (d + 1) α ^ 2)⁻¹ = a (α 0) * (base_d d (Fin.tail α) ^ 2)⁻¹ := by
          simp [hprod, a, mul_pow, mul_inv_rev, mul_comm]
        simpa [b] using this
      simpa [hsummand] using hsum₁

/-! ## The resulting nuclear spaces (axiom-free) -/

abbrev RapidDecaySeq_d (d : ℕ) : Type :=
  OSforGFF.RapidDecaySeqIndex.space (ι := Fin d → ℕ) (base := base_d d)

noncomputable instance (d : ℕ) : NuclearSpaceStd (RapidDecaySeq_d d) := by
  refine
    (OSforGFF.RapidDecaySeqIndex.Space.nuclearSpaceStd_space (ι := Fin d → ℕ)
      (base := base_d d) (hbase := fun α => one_le_base_d d α)
      (hsum := ?_))
  simpa using (summable_inv_sq_base_d d)

end RapidDecaySeqMultiIndex

end

end OSforGFF
