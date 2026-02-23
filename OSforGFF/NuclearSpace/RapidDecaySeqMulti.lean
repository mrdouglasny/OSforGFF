/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Pairing

import OSforGFF.NuclearSpace.RapidDecaySeqBase

/-!
# Multi-index rapid-decay models (via `Nat.unpair`)

This file builds concrete `base : ℕ → ℝ` functions for multi-index weights by decoding `ℕ`
into pairs (and pairs of pairs) using `Nat.unpair`.

The main lemma is that, for `base₄ n = ∏_{i=1}^4 (αᵢ(n)+1)`, we have

`Summable (fun n => (base₄ n ^ 2)⁻¹)`,

since it reindexes to the product-summable series
`∑_{α : ℕ×ℕ×ℕ×ℕ} ∏_{i=1}^4 ((αᵢ+1 : ℝ)^2)⁻¹`.

Together with `OSforGFF.NuclearSpace.RapidDecaySeqBase`, this yields an axiom-free
`NuclearSpaceStd` instance for the corresponding rapid-decay sequence space.
-/

open scoped BigOperators

namespace OSforGFF

noncomputable section

namespace RapidDecaySeqMulti

/-! ## The basic 1D summable weight `((n+1)^2)⁻¹` -/

/-- The 1D weight `a n = ((n+1)^2)⁻¹`. -/
def a (n : ℕ) : ℝ := ((n + 1 : ℝ) ^ 2)⁻¹

@[simp]
lemma a_def (n : ℕ) : a n = ((n + 1 : ℝ) ^ 2)⁻¹ := rfl

lemma a_nonneg (n : ℕ) : 0 ≤ a n := by
  have hpos : 0 < ((n + 1 : ℝ) ^ 2) := by
    have : 0 < (n + 1 : ℝ) := by exact_mod_cast (Nat.succ_pos n)
    positivity
  exact (inv_nonneg.2 (le_of_lt hpos))

theorem summable_a : Summable a := by
  have h : Summable (fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) := by
    exact (Real.summable_nat_pow_inv (p := 2)).2 (by norm_num)
  have h₁ : Summable (fun n : ℕ => (((n + 1 : ℕ) : ℝ) ^ 2)⁻¹) := by
    simpa using ((_root_.summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ) ^ 2)⁻¹) 1).2 h)
  simpa [a, Nat.cast_add_one] using h₁

/-! ## Pair and quadruple bases -/

/-- A 2D “product base” on `ℕ`, defined by decoding via `Nat.unpair`. -/
def base₂ (n : ℕ) : ℝ :=
  ((Nat.unpair n).1 + 1 : ℝ) * ((Nat.unpair n).2 + 1 : ℝ)

lemma base₂_def (n : ℕ) :
    base₂ n = ((Nat.unpair n).1 + 1 : ℝ) * ((Nat.unpair n).2 + 1 : ℝ) := rfl

lemma one_le_base₂ (n : ℕ) : (1 : ℝ) ≤ base₂ n := by
  have h1 : (1 : ℝ) ≤ ((Nat.unpair n).1 + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
  have h2 : (1 : ℝ) ≤ ((Nat.unpair n).2 + 1 : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
  simpa [base₂] using mul_le_mul h1 h2 (by positivity) (by linarith)

lemma base₂_pos (n : ℕ) : 0 < base₂ n :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_base₂ n)

lemma base₂_ne_zero (n : ℕ) : base₂ n ≠ 0 := (base₂_pos n).ne'

@[simp]
lemma inv_sq_base₂ (n : ℕ) :
    (base₂ n ^ 2)⁻¹ = a (Nat.unpair n).1 * a (Nat.unpair n).2 := by
  simp [base₂, a, mul_pow, mul_inv_rev, mul_comm]

theorem summable_inv_sq_base₂ : Summable (fun n : ℕ => (base₂ n ^ 2)⁻¹) := by
  have hprod : Summable (fun p : ℕ × ℕ => a p.1 * a p.2) := by
    exact Summable.mul_of_nonneg (f := a) (g := a) summable_a summable_a (by intro n; exact a_nonneg n)
      (by intro n; exact a_nonneg n)
  have hunpair : Summable (fun n : ℕ => a (Nat.unpair n).1 * a (Nat.unpair n).2) := by
    simpa using (Nat.pairEquiv.symm.summable_iff.mpr hprod)
  simpa [inv_sq_base₂] using hunpair

/-- A 4D “product base” on `ℕ`, decoding `n` into a pair of pairs. -/
-- A named 4-tuple pairing equivalence, for reuse in downstream constructions.
def pairEquiv₄ : (ℕ × ℕ) × (ℕ × ℕ) ≃ ℕ :=
  (Nat.pairEquiv.prodCongr Nat.pairEquiv).trans Nat.pairEquiv

/-- A 4D “product base” on `ℕ`, decoding `n` into a pair of pairs. -/
def base₄ (n : ℕ) : ℝ :=
  let p : (ℕ × ℕ) × (ℕ × ℕ) := (pairEquiv₄.symm n)
  ((p.1.1 + 1 : ℝ) * (p.1.2 + 1 : ℝ)) * ((p.2.1 + 1 : ℝ) * (p.2.2 + 1 : ℝ))

lemma base₄_def (n : ℕ) :
    base₄ n =
      let p : (ℕ × ℕ) × (ℕ × ℕ) := (pairEquiv₄.symm n)
      ((p.1.1 + 1 : ℝ) * (p.1.2 + 1 : ℝ)) * ((p.2.1 + 1 : ℝ) * (p.2.2 + 1 : ℝ)) := rfl

lemma one_le_base₄ (n : ℕ) : (1 : ℝ) ≤ base₄ n := by
  dsimp [base₄]
  set p : (ℕ × ℕ) × (ℕ × ℕ) :=
    (((Nat.pairEquiv.prodCongr Nat.pairEquiv).trans Nat.pairEquiv).symm n) with hp
  have h11 : (1 : ℝ) ≤ (p.1.1 + 1 : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
  have h12 : (1 : ℝ) ≤ (p.1.2 + 1 : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
  have h21 : (1 : ℝ) ≤ (p.2.1 + 1 : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
  have h22 : (1 : ℝ) ≤ (p.2.2 + 1 : ℝ) := by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le _))
  have h1 : (1 : ℝ) ≤ ((p.1.1 + 1 : ℝ) * (p.1.2 + 1 : ℝ)) := by
    simpa using mul_le_mul h11 h12 (by positivity) (by linarith)
  have h2 : (1 : ℝ) ≤ ((p.2.1 + 1 : ℝ) * (p.2.2 + 1 : ℝ)) := by
    simpa using mul_le_mul h21 h22 (by positivity) (by linarith)
  simpa [mul_assoc] using mul_le_mul h1 h2 (by positivity) (by linarith)

lemma base₄_pos (n : ℕ) : 0 < base₄ n :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (one_le_base₄ n)

lemma base₄_ne_zero (n : ℕ) : base₄ n ≠ 0 := (base₄_pos n).ne'

theorem summable_inv_sq_base₄ : Summable (fun n : ℕ => (base₄ n ^ 2)⁻¹) := by
  have h₂ : Summable (fun p : ℕ × ℕ => a p.1 * a p.2) := by
    exact Summable.mul_of_nonneg (f := a) (g := a) summable_a summable_a (by intro n; exact a_nonneg n)
      (by intro n; exact a_nonneg n)
  have h₂_nonneg : 0 ≤ fun p : ℕ × ℕ => a p.1 * a p.2 := by
    intro p
    exact mul_nonneg (a_nonneg p.1) (a_nonneg p.2)
  have h₄ :
      Summable (fun p : (ℕ × ℕ) × (ℕ × ℕ) =>
        (a p.1.1 * a p.1.2) * (a p.2.1 * a p.2.2)) := by
    -- `b(p.1) * b(p.2)` with `b` summable on `ℕ×ℕ`.
    let b : (ℕ × ℕ) → ℝ := fun q => a q.1 * a q.2
    have hb : Summable b := by simpa [b] using h₂
    have hb_nonneg : 0 ≤ b := by
      intro q
      exact mul_nonneg (a_nonneg q.1) (a_nonneg q.2)
    simpa [b, mul_assoc, mul_left_comm, mul_comm] using
      (Summable.mul_of_nonneg (f := b) (g := b) hb hb hb_nonneg hb_nonneg)
  -- Reindex along the explicit equivalence `(ℕ×ℕ)×(ℕ×ℕ) ≃ ℕ`.
  let e : (ℕ × ℕ) × (ℕ × ℕ) ≃ ℕ := pairEquiv₄
  have hℕ :
      Summable (fun n : ℕ =>
        (a (e.symm n).1.1 * a (e.symm n).1.2) * (a (e.symm n).2.1 * a (e.symm n).2.2)) := by
    simpa using (e.symm.summable_iff.mpr h₄)
  have hsummand :
      (fun n : ℕ => (base₄ n ^ 2)⁻¹) =
        (fun n : ℕ =>
          (a (e.symm n).1.1 * a (e.symm n).1.2) * (a (e.symm n).2.1 * a (e.symm n).2.2)) := by
    funext n
    simp [base₄, a, e, mul_pow, mul_inv_rev, mul_assoc, mul_comm, mul_left_comm]
  simpa [hsummand] using hℕ

example : Summable (fun n : ℕ => (base₂ n ^ 2)⁻¹) :=
  summable_inv_sq_base₂

example : Summable (fun n : ℕ => (base₄ n ^ 2)⁻¹) :=
  summable_inv_sq_base₄

/-! ## The resulting nuclear spaces (axiom-free) -/

abbrev RapidDecaySeq₂ : Type := OSforGFF.RapidDecaySeqBase.space base₂
abbrev RapidDecaySeq₄ : Type := OSforGFF.RapidDecaySeqBase.space base₄

noncomputable instance : NuclearSpaceStd RapidDecaySeq₂ := by
  exact (OSforGFF.RapidDecaySeqBase.Space.nuclearSpaceStd_space (base := base₂)
    (hbase := one_le_base₂) (hsum := summable_inv_sq_base₂))

noncomputable instance : NuclearSpaceStd RapidDecaySeq₄ := by
  exact (OSforGFF.RapidDecaySeqBase.Space.nuclearSpaceStd_space (base := base₄)
    (hbase := one_le_base₄) (hsum := summable_inv_sq_base₄))

end RapidDecaySeqMulti

end

end OSforGFF
