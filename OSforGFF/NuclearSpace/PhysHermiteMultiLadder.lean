/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import OSforGFF.NuclearSpace.PhysHermiteMulti
import OSforGFF.NuclearSpace.PhysHermiteSchwartzLadder
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Multi-index ladder relations (dimension-generic)

This file provides the coordinatewise raising/lowering API on multi-indices
`α : Fin d → ℕ` and proves the generic multiplication ladder identity for
`MultiHermite.eigenfunctionRealE`.
-/

open scoped BigOperators

namespace PhysLean

noncomputable section

namespace MultiHermite

variable {d : ℕ}

/-- Raise coordinate `i` of a multi-index. -/
def raise (i : Fin d) (α : Fin d → ℕ) : Fin d → ℕ :=
  Function.update α i (α i + 1)

/-- Lower coordinate `i` of a multi-index (Nat subtraction). -/
def lower (i : Fin d) (α : Fin d → ℕ) : Fin d → ℕ :=
  Function.update α i (α i - 1)

@[simp] lemma raise_apply_same (i : Fin d) (α : Fin d → ℕ) :
    raise i α i = α i + 1 := by
  simp [raise]

@[simp] lemma raise_apply_ne (i j : Fin d) (α : Fin d → ℕ) (h : j ≠ i) :
    raise i α j = α j := by
  simp [raise, h]

@[simp] lemma lower_apply_same (i : Fin d) (α : Fin d → ℕ) :
    lower i α i = α i - 1 := by
  simp [lower]

@[simp] lemma lower_apply_ne (i j : Fin d) (α : Fin d → ℕ) (h : j ≠ i) :
    lower i α j = α j := by
  simp [lower, h]

@[simp] lemma raise_apply (i j : Fin d) (α : Fin d → ℕ) :
    raise i α j = if j = i then α i + 1 else α j := by
  by_cases h : j = i
  · simp [h]
  · simp [h]

@[simp] lemma lower_apply (i j : Fin d) (α : Fin d → ℕ) :
    lower i α j = if j = i then α i - 1 else α j := by
  by_cases h : j = i
  · simp [h]
  · simp [h]

/-- Factor `eigenfunctionRealE` into the `i`-th factor times the product over `univ.erase i`. -/
lemma eigenfunctionRealE_eq_mul_prod_erase
    (ξ : ℝ) (hξ : ξ ≠ 0) (α : Fin d → ℕ) (i : Fin d) (x : E d) :
    eigenfunctionRealE (d := d) ξ hξ α x =
      PhysLean.eigenfunctionRealSchwartz ξ hξ (α i) (coordCLM d i x) *
        ∏ j ∈ (Finset.univ.erase i),
          PhysLean.eigenfunctionRealSchwartz ξ hξ (α j) (coordCLM d j x) := by
  have hmul :
      (PhysLean.eigenfunctionRealSchwartz ξ hξ (α i) (coordCLM d i x) *
        ∏ j ∈ (Finset.univ.erase i),
          PhysLean.eigenfunctionRealSchwartz ξ hξ (α j) (coordCLM d j x))
        =
      ∏ j : Fin d, PhysLean.eigenfunctionRealSchwartz ξ hξ (α j) (coordCLM d j x) := by
    simpa using
      (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin d)))
        (f := fun j : Fin d =>
          PhysLean.eigenfunctionRealSchwartz ξ hξ (α j) (coordCLM d j x))
        (a := i) (by simp))
  simpa [eigenfunctionRealE] using hmul.symm

/-- Raised-index version of `eigenfunctionRealE_eq_mul_prod_erase`. -/
lemma eigenfunctionRealE_raise_eq_mul_prod_erase
    (ξ : ℝ) (hξ : ξ ≠ 0) (α : Fin d → ℕ) (i : Fin d) (x : E d) :
    eigenfunctionRealE (d := d) ξ hξ (raise i α) x =
      PhysLean.eigenfunctionRealSchwartz ξ hξ (α i + 1) (coordCLM d i x) *
        ∏ j ∈ (Finset.univ.erase i),
          PhysLean.eigenfunctionRealSchwartz ξ hξ (α j) (coordCLM d j x) := by
  classical
  have hmul :
      (PhysLean.eigenfunctionRealSchwartz ξ hξ ((raise i α) i) (coordCLM d i x) *
        ∏ j ∈ (Finset.univ.erase i),
          PhysLean.eigenfunctionRealSchwartz ξ hξ ((raise i α) j) (coordCLM d j x))
        =
      ∏ j : Fin d, PhysLean.eigenfunctionRealSchwartz ξ hξ ((raise i α) j) (coordCLM d j x) := by
    simpa using
      (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin d)))
        (f := fun j : Fin d =>
          PhysLean.eigenfunctionRealSchwartz ξ hξ ((raise i α) j) (coordCLM d j x))
        (a := i) (by simp))
  have hmain :
      eigenfunctionRealE (d := d) ξ hξ (raise i α) x =
        PhysLean.eigenfunctionRealSchwartz ξ hξ ((raise i α) i) (coordCLM d i x) *
          ∏ j ∈ (Finset.univ.erase i),
            PhysLean.eigenfunctionRealSchwartz ξ hξ ((raise i α) j) (coordCLM d j x) := by
    simpa [eigenfunctionRealE] using hmul.symm
  refine hmain.trans ?_
  congr 1
  · simp
  · refine Finset.prod_congr rfl ?_
    intro j hj
    simp [raise_apply_ne, (Finset.mem_erase.mp hj).1]

/-- Lowered-index version of `eigenfunctionRealE_eq_mul_prod_erase`. -/
lemma eigenfunctionRealE_lower_eq_mul_prod_erase
    (ξ : ℝ) (hξ : ξ ≠ 0) (α : Fin d → ℕ) (i : Fin d) (x : E d) :
    eigenfunctionRealE (d := d) ξ hξ (lower i α) x =
      PhysLean.eigenfunctionRealSchwartz ξ hξ (α i - 1) (coordCLM d i x) *
        ∏ j ∈ (Finset.univ.erase i),
          PhysLean.eigenfunctionRealSchwartz ξ hξ (α j) (coordCLM d j x) := by
  have hmul :
      (PhysLean.eigenfunctionRealSchwartz ξ hξ ((lower i α) i) (coordCLM d i x) *
        ∏ j ∈ (Finset.univ.erase i),
          PhysLean.eigenfunctionRealSchwartz ξ hξ ((lower i α) j) (coordCLM d j x))
        =
      ∏ j : Fin d, PhysLean.eigenfunctionRealSchwartz ξ hξ ((lower i α) j) (coordCLM d j x) := by
    simpa using
      (Finset.mul_prod_erase (s := (Finset.univ : Finset (Fin d)))
        (f := fun j : Fin d =>
          PhysLean.eigenfunctionRealSchwartz ξ hξ ((lower i α) j) (coordCLM d j x))
        (a := i) (by simp))
  have hmain :
      eigenfunctionRealE (d := d) ξ hξ (lower i α) x =
        PhysLean.eigenfunctionRealSchwartz ξ hξ ((lower i α) i) (coordCLM d i x) *
          ∏ j ∈ (Finset.univ.erase i),
            PhysLean.eigenfunctionRealSchwartz ξ hξ ((lower i α) j) (coordCLM d j x) := by
    simpa [eigenfunctionRealE] using hmul.symm
  refine hmain.trans ?_
  congr 1
  · simp
  · refine Finset.prod_congr rfl ?_
    intro j hj
    simp [lower_apply_ne, (Finset.mem_erase.mp hj).1]

/-- Coordinate multiplication ladder identity in dimension `d`. -/
lemma coord_mul_eigenfunctionRealE
    (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin d) (α : Fin d → ℕ) (x : E d) :
    (coordCLM d i x) * eigenfunctionRealE (d := d) ξ hξ α x =
      (ξ / 2) * eigenfunctionRealE (d := d) ξ hξ (raise i α) x
        + (α i * ξ) * eigenfunctionRealE (d := d) ξ hξ (lower i α) x := by
  set tail : ℝ :=
    ∏ j ∈ (Finset.univ.erase i),
      PhysLean.eigenfunctionRealSchwartz ξ hξ (α j) (coordCLM d j x)
  have hsplit :
      eigenfunctionRealE (d := d) ξ hξ α x =
        PhysLean.eigenfunctionRealSchwartz ξ hξ (α i) (coordCLM d i x) * tail := by
    simpa [tail] using
      (eigenfunctionRealE_eq_mul_prod_erase (d := d) (ξ := ξ) (hξ := hξ) (α := α) (i := i) (x := x))
  have hsplitRaise :
      eigenfunctionRealE (d := d) ξ hξ (raise i α) x =
        PhysLean.eigenfunctionRealSchwartz ξ hξ (α i + 1) (coordCLM d i x) * tail := by
    simpa [tail] using
      (eigenfunctionRealE_raise_eq_mul_prod_erase (d := d) (ξ := ξ) (hξ := hξ)
        (α := α) (i := i) (x := x))
  have hsplitLower :
      eigenfunctionRealE (d := d) ξ hξ (lower i α) x =
        PhysLean.eigenfunctionRealSchwartz ξ hξ (α i - 1) (coordCLM d i x) * tail := by
    simpa [tail] using
      (eigenfunctionRealE_lower_eq_mul_prod_erase (d := d) (ξ := ξ) (hξ := hξ)
        (α := α) (i := i) (x := x))
  have h1d :
      (coordCLM d i x) * PhysLean.eigenfunctionRealSchwartz ξ hξ (α i) (coordCLM d i x) =
        (ξ / 2) * PhysLean.eigenfunctionRealSchwartz ξ hξ (α i + 1) (coordCLM d i x)
          + (α i * ξ) * PhysLean.eigenfunctionRealSchwartz ξ hξ (α i - 1) (coordCLM d i x) := by
    simpa [PhysLean.eigenfunctionRealSchwartz_apply, mul_assoc, mul_left_comm, mul_comm] using
      (PhysLean.x_mul_eigenfunctionReal (ξ := ξ) hξ (n := α i) (x := coordCLM d i x))
  calc
    (coordCLM d i x) * eigenfunctionRealE (d := d) ξ hξ α x
        = (coordCLM d i x) *
            (PhysLean.eigenfunctionRealSchwartz ξ hξ (α i) (coordCLM d i x) * tail) := by
              rw [hsplit]
    _ = ((coordCLM d i x) * PhysLean.eigenfunctionRealSchwartz ξ hξ (α i) (coordCLM d i x)) * tail := by
          ring
    _ = (((ξ / 2) * PhysLean.eigenfunctionRealSchwartz ξ hξ (α i + 1) (coordCLM d i x))
          + ((α i * ξ) * PhysLean.eigenfunctionRealSchwartz ξ hξ (α i - 1) (coordCLM d i x))) * tail := by
          rw [h1d]
    _ = (ξ / 2) * (PhysLean.eigenfunctionRealSchwartz ξ hξ (α i + 1) (coordCLM d i x) * tail)
          + (α i * ξ) *
              (PhysLean.eigenfunctionRealSchwartz ξ hξ (α i - 1) (coordCLM d i x) * tail) := by
          ring
    _ = (ξ / 2) * eigenfunctionRealE (d := d) ξ hξ (raise i α) x
          + (α i * ξ) * eigenfunctionRealE (d := d) ξ hξ (lower i α) x := by
          rw [hsplitRaise, hsplitLower]

/-! ## Coefficient-level ladder API -/

/-- Multiply a test function by coordinate `i`. -/
noncomputable def mulCoordCLM (i : Fin d) : TestFunction d →L[ℝ] TestFunction d :=
  SchwartzMap.smulLeftCLM (F := ℝ) (coordCLM d i)

@[simp] lemma mulCoordCLM_apply (i : Fin d) (f : TestFunction d) (x : E d) :
    mulCoordCLM (d := d) i f x = (coordCLM d i x) * f x := by
  have hCoord : ((coordCLM d i : E d →L[ℝ] ℝ) : E d → ℝ).HasTemperateGrowth := by
    simpa using (ContinuousLinearMap.hasTemperateGrowth (coordCLM d i))
  simpa [mulCoordCLM, smul_eq_mul] using
    (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
      (g := ((coordCLM d i : E d →L[ℝ] ℝ) : E d → ℝ)) hCoord f x)

/-- Coordinate multiplication ladder recurrence for generic multi-index coefficients. -/
lemma coeffCLM_E_mulCoord
    (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin d) (α : Fin d → ℕ) (f : TestFunction d)
    (hEigen : (eigenfunctionRealE (d := d) ξ hξ α).HasTemperateGrowth)
    (hEigenRaise : (eigenfunctionRealE (d := d) ξ hξ (raise i α)).HasTemperateGrowth)
    (hEigenLower : (eigenfunctionRealE (d := d) ξ hξ (lower i α)).HasTemperateGrowth) :
    coeffCLM_E (d := d) ξ hξ α (mulCoordCLM (d := d) i f) =
      (ξ / 2) * coeffCLM_E (d := d) ξ hξ (raise i α) f
        + (α i * ξ) * coeffCLM_E (d := d) ξ hξ (lower i α) f := by
  have hCoord : ((coordCLM d i : E d →L[ℝ] ℝ) : E d → ℝ).HasTemperateGrowth := by
    simpa using (ContinuousLinearMap.hasTemperateGrowth (coordCLM d i))
  have hDecomp :
      SchwartzMap.smulLeftCLM (F := ℝ)
          ((eigenfunctionRealE (d := d) ξ hξ α) *
            (((coordCLM d i : E d →L[ℝ] ℝ) : E d → ℝ))) f
        =
      (ξ / 2) • SchwartzMap.smulLeftCLM (F := ℝ)
          (eigenfunctionRealE (d := d) ξ hξ (raise i α)) f
        + ((α i * ξ) • SchwartzMap.smulLeftCLM (F := ℝ)
            (eigenfunctionRealE (d := d) ξ hξ (lower i α)) f) := by
    ext x
    have hL :
        (SchwartzMap.smulLeftCLM (F := ℝ)
          ((eigenfunctionRealE (d := d) ξ hξ α) *
            (((coordCLM d i : E d →L[ℝ] ℝ) : E d → ℝ))) f) x
          =
        (eigenfunctionRealE (d := d) ξ hξ α x * coordCLM d i x) * f x := by
      simpa [smul_eq_mul] using
        (SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := (eigenfunctionRealE (d := d) ξ hξ α) *
            (((coordCLM d i : E d →L[ℝ] ℝ) : E d → ℝ)))
          (hEigen.mul hCoord) f x)
    have hR :
        ((ξ / 2) • SchwartzMap.smulLeftCLM (F := ℝ)
          (eigenfunctionRealE (d := d) ξ hξ (raise i α)) f
          + ((α i * ξ) • SchwartzMap.smulLeftCLM (F := ℝ)
            (eigenfunctionRealE (d := d) ξ hξ (lower i α)) f)) x
          =
        (ξ / 2) * (eigenfunctionRealE (d := d) ξ hξ (raise i α) x * f x)
          + ((α i * ξ) *
            (eigenfunctionRealE (d := d) ξ hξ (lower i α) x * f x)) := by
      simp [smul_eq_mul,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealE (d := d) ξ hξ (raise i α)) hEigenRaise f x,
        SchwartzMap.smulLeftCLM_apply_apply (F := ℝ)
          (g := eigenfunctionRealE (d := d) ξ hξ (lower i α)) hEigenLower f x,
        mul_assoc]
    rw [hL, hR]
    calc
      (eigenfunctionRealE (d := d) ξ hξ α x * coordCLM d i x) * f x
          = (coordCLM d i x * eigenfunctionRealE (d := d) ξ hξ α x) * f x := by
              ring
      _ = ((ξ / 2) * eigenfunctionRealE (d := d) ξ hξ (raise i α) x
            + ((α i * ξ) * eigenfunctionRealE (d := d) ξ hξ (lower i α) x)) * f x := by
            have hC :
                (coordCLM d i x) * eigenfunctionRealE (d := d) ξ hξ α x =
                  (ξ / 2) * eigenfunctionRealE (d := d) ξ hξ (raise i α) x
                    + (α i * ξ) * eigenfunctionRealE (d := d) ξ hξ (lower i α) x :=
              coord_mul_eigenfunctionRealE (d := d) (ξ := ξ) (hξ := hξ) (i := i) (α := α) (x := x)
            simpa [mul_assoc] using congrArg (fun t : ℝ => t * f x) hC
      _ = (ξ / 2) * (eigenfunctionRealE (d := d) ξ hξ (raise i α) x * f x)
            + ((α i * ξ) * (eigenfunctionRealE (d := d) ξ hξ (lower i α) x * f x)) := by
              ring
  unfold coeffCLM_E mulCoordCLM
  simp only [ContinuousLinearMap.comp_apply]
  rw [SchwartzMap.smulLeftCLM_smulLeftCLM_apply (F := ℝ) hEigen hCoord f]
  rw [hDecomp]
  simp [map_add, smul_eq_mul, mul_assoc]

/-- Coordinate multiplication ladder recurrence with canonical temperate-growth witnesses. -/
lemma coeffCLM_E_mulCoord'
    (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin d) (α : Fin d → ℕ) (f : TestFunction d) :
    coeffCLM_E (d := d) ξ hξ α (mulCoordCLM (d := d) i f) =
      (ξ / 2) * coeffCLM_E (d := d) ξ hξ (raise i α) f
        + (α i * ξ) * coeffCLM_E (d := d) ξ hξ (lower i α) f := by
  refine coeffCLM_E_mulCoord (d := d) (ξ := ξ) (hξ := hξ) (i := i) (α := α) (f := f) ?_ ?_ ?_
  · exact eigenfunctionRealE_hasTemperateGrowth (d := d) (ξ := ξ) (hξ := hξ) α
  · exact eigenfunctionRealE_hasTemperateGrowth (d := d) (ξ := ξ) (hξ := hξ) (raise i α)
  · exact eigenfunctionRealE_hasTemperateGrowth (d := d) (ξ := ξ) (hξ := hξ) (lower i α)

/-- CLM form of the coordinate multiplication ladder recurrence. -/
lemma coeffCLM_E_comp_mulCoordCLM
    (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin d) (α : Fin d → ℕ) :
    (coeffCLM_E (d := d) ξ hξ α).comp (mulCoordCLM (d := d) i) =
      (ξ / 2) • coeffCLM_E (d := d) ξ hξ (raise i α)
        + (α i * ξ) • coeffCLM_E (d := d) ξ hξ (lower i α) := by
  ext f
  simpa [smul_eq_mul] using
    (coeffCLM_E_mulCoord' (d := d) (ξ := ξ) (hξ := hξ) (i := i) (α := α) (f := f))

end MultiHermite

end

end PhysLean
