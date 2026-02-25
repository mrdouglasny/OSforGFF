/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpace.PhysHermiteSpaceTime
import OSforGFF.NuclearSpace.PhysHermiteSchwartzLadder

/-!
# Multiplication ladder relations on spacetime eigenfunctions

This file lifts the 1D identity

`x * ψₙ = (ξ/2) * ψₙ₊₁ + (n*ξ) * ψₙ₋₁`

to the 4D product eigenfunctions `eigenfunctionRealSpaceTime` by acting on one coordinate.
-/

open scoped BigOperators

namespace PhysLean

noncomputable section

namespace SpaceTimeHermite

/-! ## Raising/lowering the 4-tuple index -/

open OSforGFF.RapidDecaySeqMulti SchwartzMap

/-- Increment the first component of `unpair₄ n`. -/
noncomputable def raise₀ (n : ℕ) : ℕ :=
  pairEquiv₄ ((unpair₄₁ n + 1, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n))

/-- Decrement the first component of `unpair₄ n` (using Nat subtraction). -/
noncomputable def lower₀ (n : ℕ) : ℕ :=
  pairEquiv₄ ((unpair₄₁ n - 1, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n))

/-! ### Second component -/

/-- Increment the second component of `unpair₄ n`. -/
noncomputable def raise₁ (n : ℕ) : ℕ :=
  pairEquiv₄ ((unpair₄₁ n, unpair₄₂ n + 1), (unpair₄₃ n, unpair₄₄ n))

/-- Decrement the second component of `unpair₄ n` (using Nat subtraction). -/
noncomputable def lower₁ (n : ℕ) : ℕ :=
  pairEquiv₄ ((unpair₄₁ n, unpair₄₂ n - 1), (unpair₄₃ n, unpair₄₄ n))

/-! ### Third component -/

/-- Increment the third component of `unpair₄ n`. -/
noncomputable def raise₂ (n : ℕ) : ℕ :=
  pairEquiv₄ ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n + 1, unpair₄₄ n))

/-- Decrement the third component of `unpair₄ n` (using Nat subtraction). -/
noncomputable def lower₂ (n : ℕ) : ℕ :=
  pairEquiv₄ ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n - 1, unpair₄₄ n))

/-! ### Fourth component -/

/-- Increment the fourth component of `unpair₄ n`. -/
noncomputable def raise₃ (n : ℕ) : ℕ :=
  pairEquiv₄ ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n + 1))

/-- Decrement the fourth component of `unpair₄ n` (using Nat subtraction). -/
noncomputable def lower₃ (n : ℕ) : ℕ :=
  pairEquiv₄ ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n - 1))

/-! ### Coordinate-parametric wrappers -/

/-- Increment the `i`-th decoded component of `n`. -/
noncomputable def raise (i : Fin STDimension) (n : ℕ) : ℕ :=
  match i with
  | ⟨0, _⟩ => raise₀ n
  | ⟨1, _⟩ => raise₁ n
  | ⟨2, _⟩ => raise₂ n
  | ⟨3, _⟩ => raise₃ n

/-- Decrement the `i`-th decoded component of `n` (using Nat subtraction). -/
noncomputable def lower (i : Fin STDimension) (n : ℕ) : ℕ :=
  match i with
  | ⟨0, _⟩ => lower₀ n
  | ⟨1, _⟩ => lower₁ n
  | ⟨2, _⟩ => lower₂ n
  | ⟨3, _⟩ => lower₃ n

@[simp] lemma raise_zero (n : ℕ) : raise 0 n = raise₀ n := rfl
@[simp] lemma raise_one (n : ℕ) : raise 1 n = raise₁ n := rfl
@[simp] lemma raise_two (n : ℕ) : raise 2 n = raise₂ n := rfl
@[simp] lemma raise_three (n : ℕ) : raise 3 n = raise₃ n := rfl

@[simp] lemma lower_zero (n : ℕ) : lower 0 n = lower₀ n := rfl
@[simp] lemma lower_one (n : ℕ) : lower 1 n = lower₁ n := rfl
@[simp] lemma lower_two (n : ℕ) : lower 2 n = lower₂ n := rfl
@[simp] lemma lower_three (n : ℕ) : lower 3 n = lower₃ n := rfl

@[simp] lemma unpair₄_raise₀ (n : ℕ) :
    unpair₄ (raise₀ n) = ((unpair₄₁ n + 1, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n)) := by
  simp [raise₀, unpair₄]

@[simp] lemma unpair₄_lower₀ (n : ℕ) :
    unpair₄ (lower₀ n) = ((unpair₄₁ n - 1, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n)) := by
  simp [lower₀, unpair₄]

@[simp] lemma unpair₄₁_raise₀ (n : ℕ) : unpair₄₁ (raise₀ n) = unpair₄₁ n + 1 := by
  -- extract the first component of `unpair₄_raise₀`
  simpa [unpair₄₁] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) (unpair₄_raise₀ (n := n))

@[simp] lemma unpair₄₂_raise₀ (n : ℕ) : unpair₄₂ (raise₀ n) = unpair₄₂ n := by
  simpa [unpair₄₂] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) (unpair₄_raise₀ (n := n))

@[simp] lemma unpair₄₃_raise₀ (n : ℕ) : unpair₄₃ (raise₀ n) = unpair₄₃ n := by
  simpa [unpair₄₃] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) (unpair₄_raise₀ (n := n))

@[simp] lemma unpair₄₄_raise₀ (n : ℕ) : unpair₄₄ (raise₀ n) = unpair₄₄ n := by
  simpa [unpair₄₄] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) (unpair₄_raise₀ (n := n))

@[simp] lemma unpair₄₁_lower₀ (n : ℕ) : unpair₄₁ (lower₀ n) = unpair₄₁ n - 1 := by
  simpa [unpair₄₁] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) (unpair₄_lower₀ (n := n))

@[simp] lemma unpair₄₂_lower₀ (n : ℕ) : unpair₄₂ (lower₀ n) = unpair₄₂ n := by
  simpa [unpair₄₂] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) (unpair₄_lower₀ (n := n))

@[simp] lemma unpair₄₃_lower₀ (n : ℕ) : unpair₄₃ (lower₀ n) = unpair₄₃ n := by
  simpa [unpair₄₃] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) (unpair₄_lower₀ (n := n))

@[simp] lemma unpair₄₄_lower₀ (n : ℕ) : unpair₄₄ (lower₀ n) = unpair₄₄ n := by
  simpa [unpair₄₄] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) (unpair₄_lower₀ (n := n))

@[simp] lemma unpair₄_raise₁ (n : ℕ) :
    unpair₄ (raise₁ n) = ((unpair₄₁ n, unpair₄₂ n + 1), (unpair₄₃ n, unpair₄₄ n)) := by
  simp [raise₁, unpair₄]

@[simp] lemma unpair₄_lower₁ (n : ℕ) :
    unpair₄ (lower₁ n) = ((unpair₄₁ n, unpair₄₂ n - 1), (unpair₄₃ n, unpair₄₄ n)) := by
  simp [lower₁, unpair₄]

@[simp] lemma unpair₄₁_raise₁ (n : ℕ) : unpair₄₁ (raise₁ n) = unpair₄₁ n := by
  simpa [unpair₄₁] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) (unpair₄_raise₁ (n := n))

@[simp] lemma unpair₄₂_raise₁ (n : ℕ) : unpair₄₂ (raise₁ n) = unpair₄₂ n + 1 := by
  simpa [unpair₄₂] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) (unpair₄_raise₁ (n := n))

@[simp] lemma unpair₄₃_raise₁ (n : ℕ) : unpair₄₃ (raise₁ n) = unpair₄₃ n := by
  simpa [unpair₄₃] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) (unpair₄_raise₁ (n := n))

@[simp] lemma unpair₄₄_raise₁ (n : ℕ) : unpair₄₄ (raise₁ n) = unpair₄₄ n := by
  simpa [unpair₄₄] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) (unpair₄_raise₁ (n := n))

@[simp] lemma unpair₄₁_lower₁ (n : ℕ) : unpair₄₁ (lower₁ n) = unpair₄₁ n := by
  simpa [unpair₄₁] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) (unpair₄_lower₁ (n := n))

@[simp] lemma unpair₄₂_lower₁ (n : ℕ) : unpair₄₂ (lower₁ n) = unpair₄₂ n - 1 := by
  simpa [unpair₄₂] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) (unpair₄_lower₁ (n := n))

@[simp] lemma unpair₄₃_lower₁ (n : ℕ) : unpair₄₃ (lower₁ n) = unpair₄₃ n := by
  simpa [unpair₄₃] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) (unpair₄_lower₁ (n := n))

@[simp] lemma unpair₄₄_lower₁ (n : ℕ) : unpair₄₄ (lower₁ n) = unpair₄₄ n := by
  simpa [unpair₄₄] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) (unpair₄_lower₁ (n := n))

@[simp] lemma unpair₄_raise₂ (n : ℕ) :
    unpair₄ (raise₂ n) = ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n + 1, unpair₄₄ n)) := by
  simp [raise₂, unpair₄]

@[simp] lemma unpair₄_lower₂ (n : ℕ) :
    unpair₄ (lower₂ n) = ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n - 1, unpair₄₄ n)) := by
  simp [lower₂, unpair₄]

@[simp] lemma unpair₄₁_raise₂ (n : ℕ) : unpair₄₁ (raise₂ n) = unpair₄₁ n := by
  simpa [unpair₄₁] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) (unpair₄_raise₂ (n := n))

@[simp] lemma unpair₄₂_raise₂ (n : ℕ) : unpair₄₂ (raise₂ n) = unpair₄₂ n := by
  simpa [unpair₄₂] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) (unpair₄_raise₂ (n := n))

@[simp] lemma unpair₄₃_raise₂ (n : ℕ) : unpair₄₃ (raise₂ n) = unpair₄₃ n + 1 := by
  simpa [unpair₄₃] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) (unpair₄_raise₂ (n := n))

@[simp] lemma unpair₄₄_raise₂ (n : ℕ) : unpair₄₄ (raise₂ n) = unpair₄₄ n := by
  simpa [unpair₄₄] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) (unpair₄_raise₂ (n := n))

@[simp] lemma unpair₄₁_lower₂ (n : ℕ) : unpair₄₁ (lower₂ n) = unpair₄₁ n := by
  simpa [unpair₄₁] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) (unpair₄_lower₂ (n := n))

@[simp] lemma unpair₄₂_lower₂ (n : ℕ) : unpair₄₂ (lower₂ n) = unpair₄₂ n := by
  simpa [unpair₄₂] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) (unpair₄_lower₂ (n := n))

@[simp] lemma unpair₄₃_lower₂ (n : ℕ) : unpair₄₃ (lower₂ n) = unpair₄₃ n - 1 := by
  simpa [unpair₄₃] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) (unpair₄_lower₂ (n := n))

@[simp] lemma unpair₄₄_lower₂ (n : ℕ) : unpair₄₄ (lower₂ n) = unpair₄₄ n := by
  simpa [unpair₄₄] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) (unpair₄_lower₂ (n := n))

@[simp] lemma unpair₄_raise₃ (n : ℕ) :
    unpair₄ (raise₃ n) = ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n + 1)) := by
  simp [raise₃, unpair₄]

@[simp] lemma unpair₄_lower₃ (n : ℕ) :
    unpair₄ (lower₃ n) = ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n - 1)) := by
  simp [lower₃, unpair₄]

@[simp] lemma unpair₄₁_raise₃ (n : ℕ) : unpair₄₁ (raise₃ n) = unpair₄₁ n := by
  simpa [unpair₄₁] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) (unpair₄_raise₃ (n := n))

@[simp] lemma unpair₄₂_raise₃ (n : ℕ) : unpair₄₂ (raise₃ n) = unpair₄₂ n := by
  simpa [unpair₄₂] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) (unpair₄_raise₃ (n := n))

@[simp] lemma unpair₄₃_raise₃ (n : ℕ) : unpair₄₃ (raise₃ n) = unpair₄₃ n := by
  simpa [unpair₄₃] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) (unpair₄_raise₃ (n := n))

@[simp] lemma unpair₄₄_raise₃ (n : ℕ) : unpair₄₄ (raise₃ n) = unpair₄₄ n + 1 := by
  simpa [unpair₄₄] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) (unpair₄_raise₃ (n := n))

@[simp] lemma unpair₄₁_lower₃ (n : ℕ) : unpair₄₁ (lower₃ n) = unpair₄₁ n := by
  simpa [unpair₄₁] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) (unpair₄_lower₃ (n := n))

@[simp] lemma unpair₄₂_lower₃ (n : ℕ) : unpair₄₂ (lower₃ n) = unpair₄₂ n := by
  simpa [unpair₄₂] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) (unpair₄_lower₃ (n := n))

@[simp] lemma unpair₄₃_lower₃ (n : ℕ) : unpair₄₃ (lower₃ n) = unpair₄₃ n := by
  simpa [unpair₄₃] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) (unpair₄_lower₃ (n := n))

@[simp] lemma unpair₄₄_lower₃ (n : ℕ) : unpair₄₄ (lower₃ n) = unpair₄₄ n - 1 := by
  simpa [unpair₄₄] using congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) (unpair₄_lower₃ (n := n))

/-! ## Coordinate multiplication on the 4D eigenfunctions -/

private lemma coord0_mul_eigenfunctionRealSpaceTime (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : SpaceTime) :
    (coordCLM 0 x) * eigenfunctionRealSpaceTime ξ hξ n x =
      (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₀ n) x
        + (unpair₄₁ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₀ n) x := by
  -- abbreviate the four 1D factors
  set a : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n) (coordCLM 0 x)
  set b : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n) (coordCLM 1 x)
  set c : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n) (coordCLM 2 x)
  set d : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n) (coordCLM 3 x)
  have habcd : eigenfunctionRealSpaceTime ξ hξ n x = a * b * c * d := by
    simp [eigenfunctionRealSpaceTime, a, b, c, d, mul_assoc]
  have h1 :
      (coordCLM 0 x) * a =
        (ξ / 2) * eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n + 1) (coordCLM 0 x)
          + (unpair₄₁ n * ξ) * eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n - 1) (coordCLM 0 x) := by
    simpa [a, eigenfunctionRealSchwartz_apply, mul_assoc, mul_left_comm, mul_comm] using
      (PhysLean.x_mul_eigenfunctionReal (ξ := ξ) hξ (n := unpair₄₁ n) (x := coordCLM 0 x))
  set aP : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n + 1) (coordCLM 0 x)
  set aM : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n - 1) (coordCLM 0 x)
  have habcdRaise : eigenfunctionRealSpaceTime ξ hξ (raise₀ n) x = aP * b * c * d := by
    simp [eigenfunctionRealSpaceTime, aP, b, c, d, mul_assoc]
  have habcdLower : eigenfunctionRealSpaceTime ξ hξ (lower₀ n) x = aM * b * c * d := by
    simp [eigenfunctionRealSpaceTime, aM, b, c, d, mul_assoc]
  calc
    (coordCLM 0 x) * eigenfunctionRealSpaceTime ξ hξ n x
        = (coordCLM 0 x) * (a * b * c * d) := by simp [habcd]
    _ = ((coordCLM 0 x) * a) * b * c * d := by ring
    _ = (((ξ / 2) * aP + (unpair₄₁ n * ξ) * aM) * b * c * d) := by
          rw [h1]
    _ = (ξ / 2) * (aP * b * c * d) + (unpair₄₁ n * ξ) * (aM * b * c * d) := by ring
    _ = (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₀ n) x
          + (unpair₄₁ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₀ n) x := by
          simp [habcdRaise, habcdLower]

private lemma coord1_mul_eigenfunctionRealSpaceTime (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : SpaceTime) :
    (coordCLM 1 x) * eigenfunctionRealSpaceTime ξ hξ n x =
      (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₁ n) x
        + (unpair₄₂ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₁ n) x := by
  -- abbreviate the four 1D factors
  set a : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n) (coordCLM 0 x)
  set b : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n) (coordCLM 1 x)
  set c : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n) (coordCLM 2 x)
  set d : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n) (coordCLM 3 x)
  have habcd : eigenfunctionRealSpaceTime ξ hξ n x = a * b * c * d := by
    simp [eigenfunctionRealSpaceTime, a, b, c, d, mul_assoc]
  have h1 :
      (coordCLM 1 x) * b =
        (ξ / 2) * eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n + 1) (coordCLM 1 x)
          + (unpair₄₂ n * ξ) * eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n - 1) (coordCLM 1 x) := by
    simpa [b, eigenfunctionRealSchwartz_apply, mul_assoc, mul_left_comm, mul_comm] using
      (PhysLean.x_mul_eigenfunctionReal (ξ := ξ) hξ (n := unpair₄₂ n) (x := coordCLM 1 x))
  -- name the shifted second-coordinate factors
  set bP : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n + 1) (coordCLM 1 x)
  set bM : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n - 1) (coordCLM 1 x)
  have habcdRaise : eigenfunctionRealSpaceTime ξ hξ (raise₁ n) x = a * bP * c * d := by
    simp [eigenfunctionRealSpaceTime, bP, a, c, d, mul_assoc]
  have habcdLower : eigenfunctionRealSpaceTime ξ hξ (lower₁ n) x = a * bM * c * d := by
    simp [eigenfunctionRealSpaceTime, bM, a, c, d, mul_assoc]
  calc
    (coordCLM 1 x) * eigenfunctionRealSpaceTime ξ hξ n x
        = (coordCLM 1 x) * (a * b * c * d) := by simp [habcd]
    _ = a * ((coordCLM 1 x) * b) * c * d := by ring
    _ = a * (((ξ / 2) * bP + (unpair₄₂ n * ξ) * bM) * c * d) := by
          rw [h1]
          simp [mul_assoc]
    _ = (ξ / 2) * (a * bP * c * d) + (unpair₄₂ n * ξ) * (a * bM * c * d) := by ring
    _ = (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₁ n) x
          + (unpair₄₂ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₁ n) x := by
          simp [habcdRaise, habcdLower]

private lemma coord2_mul_eigenfunctionRealSpaceTime (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : SpaceTime) :
    (coordCLM 2 x) * eigenfunctionRealSpaceTime ξ hξ n x =
      (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₂ n) x
        + (unpair₄₃ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₂ n) x := by
  set a : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n) (coordCLM 0 x)
  set b : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n) (coordCLM 1 x)
  set c : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n) (coordCLM 2 x)
  set d : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n) (coordCLM 3 x)
  have habcd : eigenfunctionRealSpaceTime ξ hξ n x = a * b * c * d := by
    simp [eigenfunctionRealSpaceTime, a, b, c, d, mul_assoc]
  have h1 :
      (coordCLM 2 x) * c =
        (ξ / 2) * eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n + 1) (coordCLM 2 x)
          + (unpair₄₃ n * ξ) * eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n - 1) (coordCLM 2 x) := by
    simpa [c, eigenfunctionRealSchwartz_apply, mul_assoc, mul_left_comm, mul_comm] using
      (PhysLean.x_mul_eigenfunctionReal (ξ := ξ) hξ (n := unpair₄₃ n) (x := coordCLM 2 x))
  set cP : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n + 1) (coordCLM 2 x)
  set cM : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n - 1) (coordCLM 2 x)
  have habcdRaise : eigenfunctionRealSpaceTime ξ hξ (raise₂ n) x = a * b * cP * d := by
    simp [eigenfunctionRealSpaceTime, cP, a, b, d, mul_assoc]
  have habcdLower : eigenfunctionRealSpaceTime ξ hξ (lower₂ n) x = a * b * cM * d := by
    simp [eigenfunctionRealSpaceTime, cM, a, b, d, mul_assoc]
  calc
    (coordCLM 2 x) * eigenfunctionRealSpaceTime ξ hξ n x
        = (coordCLM 2 x) * (a * b * c * d) := by simp [habcd]
    _ = a * b * ((coordCLM 2 x) * c) * d := by ring
    _ = a * b * (((ξ / 2) * cP + (unpair₄₃ n * ξ) * cM) * d) := by
          rw [h1]
          simp [mul_assoc]
    _ = (ξ / 2) * (a * b * cP * d) + (unpair₄₃ n * ξ) * (a * b * cM * d) := by ring
    _ = (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₂ n) x
          + (unpair₄₃ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₂ n) x := by
          simp [habcdRaise, habcdLower]

private lemma coord3_mul_eigenfunctionRealSpaceTime (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (x : SpaceTime) :
    (coordCLM 3 x) * eigenfunctionRealSpaceTime ξ hξ n x =
      (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₃ n) x
        + (unpair₄₄ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₃ n) x := by
  set a : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₁ n) (coordCLM 0 x)
  set b : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₂ n) (coordCLM 1 x)
  set c : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₃ n) (coordCLM 2 x)
  set d : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n) (coordCLM 3 x)
  have habcd : eigenfunctionRealSpaceTime ξ hξ n x = a * b * c * d := by
    simp [eigenfunctionRealSpaceTime, a, b, c, d, mul_assoc]
  have h1 :
      (coordCLM 3 x) * d =
        (ξ / 2) * eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n + 1) (coordCLM 3 x)
          + (unpair₄₄ n * ξ) * eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n - 1) (coordCLM 3 x) := by
    simpa [d, eigenfunctionRealSchwartz_apply, mul_assoc, mul_left_comm, mul_comm] using
      (PhysLean.x_mul_eigenfunctionReal (ξ := ξ) hξ (n := unpair₄₄ n) (x := coordCLM 3 x))
  set dP : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n + 1) (coordCLM 3 x)
  set dM : ℝ := eigenfunctionRealSchwartz ξ hξ (unpair₄₄ n - 1) (coordCLM 3 x)
  have habcdRaise : eigenfunctionRealSpaceTime ξ hξ (raise₃ n) x = a * b * c * dP := by
    simp [eigenfunctionRealSpaceTime, dP, a, b, c, mul_assoc]
  have habcdLower : eigenfunctionRealSpaceTime ξ hξ (lower₃ n) x = a * b * c * dM := by
    simp [eigenfunctionRealSpaceTime, dM, a, b, c, mul_assoc]
  calc
    (coordCLM 3 x) * eigenfunctionRealSpaceTime ξ hξ n x
        = (coordCLM 3 x) * (a * b * c * d) := by simp [habcd]
    _ = a * b * c * ((coordCLM 3 x) * d) := by ring
    _ = a * b * c * ((ξ / 2) * dP + (unpair₄₄ n * ξ) * dM) := by
          rw [h1]
    _ = (ξ / 2) * (a * b * c * dP) + (unpair₄₄ n * ξ) * (a * b * c * dM) := by ring
    _ = (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise₃ n) x
          + (unpair₄₄ n * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower₃ n) x := by
          simp [habcdRaise, habcdLower]

/-- Coordinate-uniform multiplication ladder identity on spacetime eigenfunctions. -/
lemma coord_mul_eigenfunctionRealSpaceTime (ξ : ℝ) (hξ : ξ ≠ 0)
    (i : Fin STDimension) (n : ℕ) (x : SpaceTime) :
    (coordCLM i x) * eigenfunctionRealSpaceTime ξ hξ n x =
      (ξ / 2) * eigenfunctionRealSpaceTime ξ hξ (raise i n) x
        + ((((idx n i : ℕ) : ℝ) * ξ) * eigenfunctionRealSpaceTime ξ hξ (lower i n) x) := by
  fin_cases i
  · simpa [raise, lower, idx] using
      (coord0_mul_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) (n := n) (x := x))
  · simpa [raise, lower, idx] using
      (coord1_mul_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) (n := n) (x := x))
  · simpa [raise, lower, idx] using
      (coord2_mul_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) (n := n) (x := x))
  · simpa [raise, lower, idx] using
      (coord3_mul_eigenfunctionRealSpaceTime (ξ := ξ) (hξ := hξ) (n := n) (x := x))

end SpaceTimeHermite

end

end PhysLean
