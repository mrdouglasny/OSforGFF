import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffL2Bounds
import OSforGFF.NuclearSpace.PhysHermiteSpaceTimeCoeffSeminorm

/-!
# Operator bounds in coefficient seminorms

This file collects basic estimates showing that applying the coordinatewise ladder operators
(`raiseOpCLM`, `lowerOpCLM`) increases the coefficient seminorm index by at most `1`, up to a
uniform constant.

These are intended as building blocks for the (hard) comparison
`schwartzSeminormSeq ≲ coeffSeminormSeq`.
-/

open scoped BigOperators NNReal ENNReal

namespace PhysLean

noncomputable section

namespace SpaceTimeHermite

open MeasureTheory

local notation "H" => ℓ²(ℕ, ℝ)
local notation "base₄" => OSforGFF.RapidDecaySeqMulti.base₄

/-! ## `raise` after `lower` (when the component is positive) -/

private lemma unpair₄_eta (n : ℕ) :
    ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n)) = unpair₄ n := by
  ext <;> rfl

lemma raise₀_lower₀_of_pos {n : ℕ} (hn : 0 < unpair₄₁ n) : raise₀ (lower₀ n) = n := by
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  change unpair₄ (raise₀ (lower₀ n)) = unpair₄ n
  rw [unpair₄_raise₀]
  rw [← unpair₄_eta n]
  have hsub : unpair₄₁ n - 1 + 1 = unpair₄₁ n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  simp [hsub]

lemma raise₁_lower₁_of_pos {n : ℕ} (hn : 0 < unpair₄₂ n) : raise₁ (lower₁ n) = n := by
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  change unpair₄ (raise₁ (lower₁ n)) = unpair₄ n
  rw [unpair₄_raise₁]
  rw [← unpair₄_eta n]
  have hsub : unpair₄₂ n - 1 + 1 = unpair₄₂ n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  simp [hsub]

lemma raise₂_lower₂_of_pos {n : ℕ} (hn : 0 < unpair₄₃ n) : raise₂ (lower₂ n) = n := by
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  change unpair₄ (raise₂ (lower₂ n)) = unpair₄ n
  rw [unpair₄_raise₂]
  rw [← unpair₄_eta n]
  have hsub : unpair₄₃ n - 1 + 1 = unpair₄₃ n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  simp [hsub]

lemma raise₃_lower₃_of_pos {n : ℕ} (hn : 0 < unpair₄₄ n) : raise₃ (lower₃ n) = n := by
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  change unpair₄ (raise₃ (lower₃ n)) = unpair₄ n
  rw [unpair₄_raise₃]
  rw [← unpair₄_eta n]
  have hsub : unpair₄₄ n - 1 + 1 = unpair₄₄ n :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  simp [hsub]

/-! ## Normalized coefficient action of `raiseOpCLM` at an arbitrary index -/

lemma normalizedCoeffCLM_SpaceTime_raiseOpCLM0 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (0 : Fin STDimension) f) =
      Real.sqrt ((2 : ℝ) * (unpair₄₁ n : ℝ)) *
        normalizedCoeffCLM_SpaceTime ξ hξ (lower₀ n) f := by
  -- If the first component is `0`, this is immediate from the unnormalized coefficient ladder.
  classical
  by_cases h0 : unpair₄₁ n = 0
  · -- `coeffCLM ... = 0` since it has a factor `unpair₄₁ n`.
    have hcoeff0 :
        coeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (0 : Fin STDimension) f) = 0 := by
      -- rewrite using the coefficient ladder, then use `h0`
      rw [coeffCLM_SpaceTime_raiseOpCLM0 (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
      simp [h0]
    -- unfold normalized coefficients and simplify
    -- keep `raiseOpCLM` opaque so we can use `hcoeff0`
    simp [normalizedCoeffCLM_SpaceTime_apply, hcoeff0, h0, -coeffCLM_SpaceTime_apply, -raiseOpCLM_apply]
  · have hpos : 0 < unpair₄₁ n := Nat.pos_of_ne_zero h0
    -- rewrite the target index as `raise₀ (lower₀ n)` and use the existing raised-index lemma
    have hn : raise₀ (lower₀ n) = n := raise₀_lower₀_of_pos (n := n) hpos
    have hidxNat : unpair₄₁ (lower₀ n) + 1 = unpair₄₁ n := by
      -- `unpair₄₁ (lower₀ n) = unpair₄₁ n - 1`, and `a - 1 + 1 = a` since `0 < a`.
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    -- apply the raised-index identity with `n := lower₀ n`
    have hstep :=
      normalizedCoeffCLM_SpaceTime_raiseOpCLM0_raise₀ (ξ := ξ) (hξ := hξ) (n := lower₀ n) (f := f)
    -- rewrite `raise₀ (lower₀ n)` to `n` and rewrite the scalar factor at the Nat level
    rw [hidxNat] at hstep
    rw [hn] at hstep
    simpa using hstep

lemma normalizedCoeffCLM_SpaceTime_raiseOpCLM1 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (1 : Fin STDimension) f) =
      Real.sqrt ((2 : ℝ) * (unpair₄₂ n : ℝ)) *
        normalizedCoeffCLM_SpaceTime ξ hξ (lower₁ n) f := by
  classical
  by_cases h0 : unpair₄₂ n = 0
  · have hcoeff0 :
        coeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (1 : Fin STDimension) f) = 0 := by
      rw [coeffCLM_SpaceTime_raiseOpCLM1 (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
      simp [h0]
    simp [normalizedCoeffCLM_SpaceTime_apply, hcoeff0, h0, -coeffCLM_SpaceTime_apply, -raiseOpCLM_apply]
  · have hpos : 0 < unpair₄₂ n := Nat.pos_of_ne_zero h0
    have hn : raise₁ (lower₁ n) = n := raise₁_lower₁_of_pos (n := n) hpos
    have hidxNat : unpair₄₂ (lower₁ n) + 1 = unpair₄₂ n := by
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    have hstep :=
      normalizedCoeffCLM_SpaceTime_raiseOpCLM1_raise₁ (ξ := ξ) (hξ := hξ) (n := lower₁ n) (f := f)
    rw [hidxNat] at hstep
    rw [hn] at hstep
    simpa using hstep

lemma normalizedCoeffCLM_SpaceTime_raiseOpCLM2 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (2 : Fin STDimension) f) =
      Real.sqrt ((2 : ℝ) * (unpair₄₃ n : ℝ)) *
        normalizedCoeffCLM_SpaceTime ξ hξ (lower₂ n) f := by
  classical
  by_cases h0 : unpair₄₃ n = 0
  · have hcoeff0 :
        coeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (2 : Fin STDimension) f) = 0 := by
      rw [coeffCLM_SpaceTime_raiseOpCLM2 (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
      simp [h0]
    simp [normalizedCoeffCLM_SpaceTime_apply, hcoeff0, h0, -coeffCLM_SpaceTime_apply, -raiseOpCLM_apply]
  · have hpos : 0 < unpair₄₃ n := Nat.pos_of_ne_zero h0
    have hn : raise₂ (lower₂ n) = n := raise₂_lower₂_of_pos (n := n) hpos
    have hidxNat : unpair₄₃ (lower₂ n) + 1 = unpair₄₃ n := by
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    have hstep :=
      normalizedCoeffCLM_SpaceTime_raiseOpCLM2_raise₂ (ξ := ξ) (hξ := hξ) (n := lower₂ n) (f := f)
    rw [hidxNat] at hstep
    rw [hn] at hstep
    simpa using hstep

lemma normalizedCoeffCLM_SpaceTime_raiseOpCLM3 (ξ : ℝ) (hξ : ξ ≠ 0) (n : ℕ) (f : TestFunction) :
    normalizedCoeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (3 : Fin STDimension) f) =
      Real.sqrt ((2 : ℝ) * (unpair₄₄ n : ℝ)) *
        normalizedCoeffCLM_SpaceTime ξ hξ (lower₃ n) f := by
  classical
  by_cases h0 : unpair₄₄ n = 0
  · have hcoeff0 :
        coeffCLM_SpaceTime ξ hξ n (raiseOpCLM ξ (3 : Fin STDimension) f) = 0 := by
      rw [coeffCLM_SpaceTime_raiseOpCLM3 (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
      simp [h0]
    simp [normalizedCoeffCLM_SpaceTime_apply, hcoeff0, h0, -coeffCLM_SpaceTime_apply, -raiseOpCLM_apply]
  · have hpos : 0 < unpair₄₄ n := Nat.pos_of_ne_zero h0
    have hn : raise₃ (lower₃ n) = n := raise₃_lower₃_of_pos (n := n) hpos
    have hidxNat : unpair₄₄ (lower₃ n) + 1 = unpair₄₄ n := by
      simpa [Nat.sub_add_cancel (Nat.succ_le_of_lt hpos)]
    have hstep :=
      normalizedCoeffCLM_SpaceTime_raiseOpCLM3_raise₃ (ξ := ξ) (hξ := hξ) (n := lower₃ n) (f := f)
    rw [hidxNat] at hstep
    rw [hn] at hstep
    simpa using hstep

/-! ## Comparison lemmas for the 4D weight `base₄` under raising indices -/

lemma base₄_le_base₄_raise₀ (n : ℕ) : base₄ n ≤ base₄ (raise₀ n) := by
  have hr :
      0 ≤ ((unpair₄₃ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) := by
    positivity
  have h : (unpair₄₁ n : ℝ) + 1 ≤ (unpair₄₁ n : ℝ) + 1 + 1 := by linarith
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm,
    unpair₄₁_raise₀, unpair₄₂_raise₀, unpair₄₃_raise₀, unpair₄₄_raise₀] using
    (mul_le_mul_of_nonneg_right h hr)

lemma base₄_le_base₄_raise₁ (n : ℕ) : base₄ n ≤ base₄ (raise₁ n) := by
  have ha : 0 ≤ (unpair₄₁ n : ℝ) + 1 := by positivity
  have hb : 0 ≤ (unpair₄₃ n : ℝ) + 1 := by positivity
  have hd : 0 ≤ (unpair₄₄ n : ℝ) + 1 := by positivity
  have h : (unpair₄₂ n : ℝ) + 1 ≤ (unpair₄₂ n : ℝ) + 1 + 1 := by linarith
  have hcd :
      ((unpair₄₂ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1) ≤
        ((unpair₄₂ n : ℝ) + 1 + 1) * ((unpair₄₄ n : ℝ) + 1) := by
    exact mul_le_mul_of_nonneg_right h hd
  have hB :
      ((unpair₄₃ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) ≤
        ((unpair₄₃ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1 + 1) * ((unpair₄₄ n : ℝ) + 1)) := by
    exact mul_le_mul_of_nonneg_left hcd hb
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm,
    unpair₄₁_raise₁, unpair₄₂_raise₁, unpair₄₃_raise₁, unpair₄₄_raise₁] using
    (mul_le_mul_of_nonneg_left hB ha)

lemma base₄_le_base₄_raise₂ (n : ℕ) : base₄ n ≤ base₄ (raise₂ n) := by
  have hab : 0 ≤ (unpair₄₁ n : ℝ) + 1 := by positivity
  have hb' : 0 ≤ (unpair₄₂ n : ℝ) + 1 := by positivity
  have hd : 0 ≤ (unpair₄₄ n : ℝ) + 1 := by positivity
  have h : (unpair₄₃ n : ℝ) + 1 ≤ (unpair₄₃ n : ℝ) + 1 + 1 := by linarith
  have hcd :
      ((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1) ≤
        ((unpair₄₃ n : ℝ) + 1 + 1) * ((unpair₄₄ n : ℝ) + 1) := by
    exact mul_le_mul_of_nonneg_right h hd
  have hR :
      ((unpair₄₁ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1))) ≤
        ((unpair₄₁ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * (((unpair₄₃ n : ℝ) + 1 + 1) * ((unpair₄₄ n : ℝ) + 1))) := by
    -- multiply `hcd` on the left by the nonnegative factor `(1+u1)*(1+u2)`
    have hcd' :
        ((unpair₄₂ n : ℝ) + 1) * (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) ≤
          ((unpair₄₂ n : ℝ) + 1) * (((unpair₄₃ n : ℝ) + 1 + 1) * ((unpair₄₄ n : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_left hcd hb'
    exact mul_le_mul_of_nonneg_left hcd' hab
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm,
    unpair₄₁_raise₂, unpair₄₂_raise₂, unpair₄₃_raise₂, unpair₄₄_raise₂] using hR

lemma base₄_le_base₄_raise₃ (n : ℕ) : base₄ n ≤ base₄ (raise₃ n) := by
  have ha : 0 ≤ (unpair₄₁ n : ℝ) + 1 := by positivity
  have hb : 0 ≤ (unpair₄₂ n : ℝ) + 1 := by positivity
  have hc : 0 ≤ (unpair₄₃ n : ℝ) + 1 := by positivity
  have h : (unpair₄₄ n : ℝ) + 1 ≤ (unpair₄₄ n : ℝ) + 1 + 1 := by linarith
  have hcd :
      ((unpair₄₂ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1) ≤
        ((unpair₄₂ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1 + 1) := by
    exact mul_le_mul_of_nonneg_left h hb
  have h2 :
      ((unpair₄₃ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) ≤
        ((unpair₄₃ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1 + 1)) := by
    exact mul_le_mul_of_nonneg_left hcd hc
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm,
    unpair₄₁_raise₃, unpair₄₂_raise₃, unpair₄₃_raise₃, unpair₄₄_raise₃] using
    (mul_le_mul_of_nonneg_left h2 ha)

/-! ## Upper bounds for `base₄ (raiseᵢ n)` in terms of `base₄ n` -/

lemma base₄_raise₀_le_two_mul_base₄ (n : ℕ) : base₄ (raise₀ n) ≤ (2 : ℝ) * base₄ n := by
  have hr :
      0 ≤ ((unpair₄₂ n : ℝ) + 1) * (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) := by
    positivity
  have h : (unpair₄₁ n : ℝ) + 1 + 1 ≤ (2 : ℝ) * ((unpair₄₁ n : ℝ) + 1) := by
    have : (1 : ℝ) ≤ (unpair₄₁ n : ℝ) + 1 := by
      have : 0 ≤ (unpair₄₁ n : ℝ) := by positivity
      linarith
    -- `a+1 ≤ 2*a` is equivalent to `1 ≤ a`
    linarith
  -- multiply by the remaining nonnegative factors
  have hmul :
      ((unpair₄₁ n : ℝ) + 1 + 1) * (((unpair₄₂ n : ℝ) + 1) * (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1))) ≤
        ((2 : ℝ) * ((unpair₄₁ n : ℝ) + 1)) * (((unpair₄₂ n : ℝ) + 1) * (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_right h hr
  -- rearrange to match `base₄_eq_unpair₄`
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm,
    unpair₄₁_raise₀, unpair₄₂_raise₀, unpair₄₃_raise₀, unpair₄₄_raise₀] using hmul

lemma base₄_raise₁_le_two_mul_base₄ (n : ℕ) : base₄ (raise₁ n) ≤ (2 : ℝ) * base₄ n := by
  have hr :
      0 ≤ ((unpair₄₁ n : ℝ) + 1) * (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) := by
    positivity
  have h : (unpair₄₂ n : ℝ) + 1 + 1 ≤ (2 : ℝ) * ((unpair₄₂ n : ℝ) + 1) := by
    have : (1 : ℝ) ≤ (unpair₄₂ n : ℝ) + 1 := by
      have : 0 ≤ (unpair₄₂ n : ℝ) := by positivity
      linarith
    linarith
  have hmul :
      ((unpair₄₂ n : ℝ) + 1 + 1) * (((unpair₄₁ n : ℝ) + 1) * (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1))) ≤
        ((2 : ℝ) * ((unpair₄₂ n : ℝ) + 1)) * (((unpair₄₁ n : ℝ) + 1) * (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_right h hr
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm,
    unpair₄₁_raise₁, unpair₄₂_raise₁, unpair₄₃_raise₁, unpair₄₄_raise₁] using hmul

lemma base₄_raise₂_le_two_mul_base₄ (n : ℕ) : base₄ (raise₂ n) ≤ (2 : ℝ) * base₄ n := by
  have hr :
      0 ≤ ((unpair₄₁ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) := by
    positivity
  have h : (unpair₄₃ n : ℝ) + 1 + 1 ≤ (2 : ℝ) * ((unpair₄₃ n : ℝ) + 1) := by
    have : (1 : ℝ) ≤ (unpair₄₃ n : ℝ) + 1 := by
      have : 0 ≤ (unpair₄₃ n : ℝ) := by positivity
      linarith
    linarith
  have hmul :
      ((unpair₄₃ n : ℝ) + 1 + 1) * (((unpair₄₁ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1))) ≤
        ((2 : ℝ) * ((unpair₄₃ n : ℝ) + 1)) * (((unpair₄₁ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_right h hr
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm,
    unpair₄₁_raise₂, unpair₄₂_raise₂, unpair₄₃_raise₂, unpair₄₄_raise₂] using hmul

lemma base₄_raise₃_le_two_mul_base₄ (n : ℕ) : base₄ (raise₃ n) ≤ (2 : ℝ) * base₄ n := by
  have hr :
      0 ≤ ((unpair₄₁ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * ((unpair₄₃ n : ℝ) + 1)) := by
    positivity
  have h : (unpair₄₄ n : ℝ) + 1 + 1 ≤ (2 : ℝ) * ((unpair₄₄ n : ℝ) + 1) := by
    have : (1 : ℝ) ≤ (unpair₄₄ n : ℝ) + 1 := by
      have : 0 ≤ (unpair₄₄ n : ℝ) := by positivity
      linarith
    linarith
  have hmul :
      ((unpair₄₄ n : ℝ) + 1 + 1) * (((unpair₄₁ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * ((unpair₄₃ n : ℝ) + 1))) ≤
        ((2 : ℝ) * ((unpair₄₄ n : ℝ) + 1)) * (((unpair₄₁ n : ℝ) + 1) * (((unpair₄₂ n : ℝ) + 1) * ((unpair₄₃ n : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_right h hr
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm,
    unpair₄₁_raise₃, unpair₄₂_raise₃, unpair₄₃_raise₃, unpair₄₄_raise₃] using hmul

/-! ## Bounding single coordinate factors by `base₄` -/

lemma unpair₄₁_add_one_le_base₄ (n : ℕ) : (unpair₄₁ n : ℝ) + 1 ≤ base₄ n := by
  have h2 : (1 : ℝ) ≤ (unpair₄₂ n : ℝ) + 1 := by
    have : 0 ≤ (unpair₄₂ n : ℝ) := by positivity
    linarith
  have h3 : (1 : ℝ) ≤ (unpair₄₃ n : ℝ) + 1 := by
    have : 0 ≤ (unpair₄₃ n : ℝ) := by positivity
    linarith
  have h4 : (1 : ℝ) ≤ (unpair₄₄ n : ℝ) + 1 := by
    have : 0 ≤ (unpair₄₄ n : ℝ) := by positivity
    linarith
  have h12 :
      (unpair₄₁ n : ℝ) + 1 ≤ ((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1) := by
    exact le_mul_of_one_le_right (by positivity) h2
  have h34 :
      (1 : ℝ) ≤ ((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1) := by
    have : (unpair₄₃ n : ℝ) + 1 ≤ ((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1) := by
      exact le_mul_of_one_le_right (by positivity) h4
    exact le_trans h3 this
  have hmul :
      ((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1) ≤
        (((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1)) *
          (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) := by
    exact le_mul_of_one_le_right (by positivity) h34
  have h1234 :
      (unpair₄₁ n : ℝ) + 1 ≤
        (((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1)) *
          (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) := by
    exact le_trans h12 hmul
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm] using h1234

lemma unpair₄₂_add_one_le_base₄ (n : ℕ) : (unpair₄₂ n : ℝ) + 1 ≤ base₄ n := by
  -- symmetric to the first component
  have h1 : (1 : ℝ) ≤ (unpair₄₁ n : ℝ) + 1 := by
    have : 0 ≤ (unpair₄₁ n : ℝ) := by positivity
    linarith
  have h3 : (1 : ℝ) ≤ (unpair₄₃ n : ℝ) + 1 := by
    have : 0 ≤ (unpair₄₃ n : ℝ) := by positivity
    linarith
  have h4 : (1 : ℝ) ≤ (unpair₄₄ n : ℝ) + 1 := by
    have : 0 ≤ (unpair₄₄ n : ℝ) := by positivity
    linarith
  have h12 :
      (unpair₄₂ n : ℝ) + 1 ≤ ((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1) := by
    -- multiply on the left by `(unpair₄₁ n + 1) ≥ 1`
    exact le_mul_of_one_le_left (by positivity) h1
  have h34 :
      (1 : ℝ) ≤ ((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1) := by
    have : (unpair₄₃ n : ℝ) + 1 ≤ ((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1) := by
      exact le_mul_of_one_le_right (by positivity) h4
    exact le_trans h3 this
  have hmul :
      ((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1) ≤
        (((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1)) *
          (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) := by
    exact le_mul_of_one_le_right (by positivity) h34
  have h1234 :
      (unpair₄₂ n : ℝ) + 1 ≤
        (((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1)) *
          (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) := by
    exact le_trans h12 hmul
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm] using h1234

lemma unpair₄₃_add_one_le_base₄ (n : ℕ) : (unpair₄₃ n : ℝ) + 1 ≤ base₄ n := by
  -- reduce to the previous lemma by commutativity
  -- the product defining `base₄` is symmetric in the last two factors
  have h :
      (unpair₄₃ n : ℝ) + 1 ≤
        (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) *
          (((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1)) := by
    -- apply `unpair₄₁_add_one_le_base₄` to the swapped tuple via commutativity
    -- (a quick, direct proof is shorter than an explicit symmetry lemma)
    have h4 : (1 : ℝ) ≤ (unpair₄₄ n : ℝ) + 1 := by
      have : 0 ≤ (unpair₄₄ n : ℝ) := by positivity
      linarith
    have h12 : (1 : ℝ) ≤ ((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1) := by
      have h1 : (1 : ℝ) ≤ (unpair₄₁ n : ℝ) + 1 := by
        have : 0 ≤ (unpair₄₁ n : ℝ) := by positivity
        linarith
      have : (unpair₄₁ n : ℝ) + 1 ≤ ((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1) := by
        have h2 : (1 : ℝ) ≤ (unpair₄₂ n : ℝ) + 1 := by
          have : 0 ≤ (unpair₄₂ n : ℝ) := by positivity
          linarith
        exact le_mul_of_one_le_right (by positivity) h2
      exact le_trans h1 this
    have h34 :
        (unpair₄₃ n : ℝ) + 1 ≤ ((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1) := by
      exact le_mul_of_one_le_right (by positivity) h4
    have hmul :
        ((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1) ≤
          (((unpair₄₃ n : ℝ) + 1) * ((unpair₄₄ n : ℝ) + 1)) *
            (((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1)) := by
      exact le_mul_of_one_le_right (by positivity) h12
    exact le_trans h34 hmul
  -- rewrite `base₄` and commute factors
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm] using h

lemma unpair₄₄_add_one_le_base₄ (n : ℕ) : (unpair₄₄ n : ℝ) + 1 ≤ base₄ n := by
  -- same as the previous lemma, swapping the last two components
  have h :
      (unpair₄₄ n : ℝ) + 1 ≤
        (((unpair₄₄ n : ℝ) + 1) * ((unpair₄₃ n : ℝ) + 1)) *
          (((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1)) := by
    -- start with `(unpair₄₄+1) ≤ (unpair₄₄+1)*(unpair₄₃+1)` then multiply by the remaining ≥1
    have h3 : (1 : ℝ) ≤ (unpair₄₃ n : ℝ) + 1 := by
      have : 0 ≤ (unpair₄₃ n : ℝ) := by positivity
      linarith
    have h12 : (1 : ℝ) ≤ ((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1) := by
      have h1 : (1 : ℝ) ≤ (unpair₄₁ n : ℝ) + 1 := by
        have : 0 ≤ (unpair₄₁ n : ℝ) := by positivity
        linarith
      have : (unpair₄₁ n : ℝ) + 1 ≤ ((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1) := by
        have h2 : (1 : ℝ) ≤ (unpair₄₂ n : ℝ) + 1 := by
          have : 0 ≤ (unpair₄₂ n : ℝ) := by positivity
          linarith
        exact le_mul_of_one_le_right (by positivity) h2
      exact le_trans h1 this
    have h43 :
        (unpair₄₄ n : ℝ) + 1 ≤ ((unpair₄₄ n : ℝ) + 1) * ((unpair₄₃ n : ℝ) + 1) := by
      exact le_mul_of_one_le_right (by positivity) h3
    have hmul :
        ((unpair₄₄ n : ℝ) + 1) * ((unpair₄₃ n : ℝ) + 1) ≤
          (((unpair₄₄ n : ℝ) + 1) * ((unpair₄₃ n : ℝ) + 1)) *
            (((unpair₄₁ n : ℝ) + 1) * ((unpair₄₂ n : ℝ) + 1)) := by
      exact le_mul_of_one_le_right (by positivity) h12
    exact le_trans h43 hmul
  simpa [base₄_eq_unpair₄, mul_assoc, mul_left_comm, mul_comm] using h

/-! ## (Work in progress) Bounding ladder operators on coefficient seminorms -/

-- These ladder-operator bounds are one input for proving the reverse seminorm comparison
-- `OSforGFF.schwartzSeminormSeq ≲ coeffSeminormSeq ξ hξ`; see
-- `OSforGFF.NuclearSpace.PhysHermiteSpaceTimeSchwartzToCoeffBound`.

/-!
## Bounding `raiseOpCLM` / `lowerOpCLM` in coefficient seminorms

The goal here is to show inequalities of the form

`coeffSeminormSeq k (raiseOpCLM … f) ≤ C(k) * coeffSeminormSeq (k+1) f`,

and similarly for `lowerOpCLM`, by working on the weighted `ℓ²` coordinates.
-/

-- We will use the `ℓ²`-model norms.
open scoped Real

private lemma sqrt_two_pos : (0 : ℝ) < Real.sqrt 2 := by
  have : (0 : ℝ) < (2 : ℝ) := by norm_num
  simpa using Real.sqrt_pos.2 this

/-! ### Small norm-algebra lemmas (real scalars) -/

private lemma norm_mul_sqrt_mul_sq (a t c : ℝ) (ht0 : 0 ≤ t) :
    ‖a * Real.sqrt t * c‖ ^ (2 : ℕ) = a ^ (2 : ℕ) * t * ‖c‖ ^ (2 : ℕ) := by
  have ha : |a| * |a| = a * a := by
    calc
      |a| * |a| = |a * a| := by
        simpa [abs_mul] using (abs_mul a a).symm
      _ = a * a := by
        simp [abs_of_nonneg (mul_self_nonneg a)]
  have hc : |c| * |c| = c * c := by
    calc
      |c| * |c| = |c * c| := by
        simpa [abs_mul] using (abs_mul c c).symm
      _ = c * c := by
        simp [abs_of_nonneg (mul_self_nonneg c)]
  have hs : |Real.sqrt t| = Real.sqrt t := by
    have : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
    simpa [abs_of_nonneg this]
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht0
  have hcnorm : ‖c‖ ^ (2 : ℕ) = c * c := by
    -- `‖c‖ = |c|` and use `hc`
    simpa [Real.norm_eq_abs, pow_two, hc, mul_assoc] using hc
  calc
    ‖a * Real.sqrt t * c‖ ^ (2 : ℕ)
        = |a * Real.sqrt t * c| ^ (2 : ℕ) := by
            simp [Real.norm_eq_abs]
    _ = (|a| * |Real.sqrt t| * |c|) ^ (2 : ℕ) := by
            simp [abs_mul, mul_assoc, mul_left_comm, mul_comm]
    _ = (|a| * |Real.sqrt t| * |c|) * (|a| * |Real.sqrt t| * |c|) := by
            simp [pow_two]
    _ = (|a| * |a|) * (|Real.sqrt t| * |Real.sqrt t|) * (|c| * |c|) := by
            ring_nf
    _ = (a * a) * (Real.sqrt t * Real.sqrt t) * (c * c) := by
            simp [ha, hc, hs]
    _ = (a * a) * t * (c * c) := by
            simpa [mul_assoc] using congrArg (fun x => (a * a) * x * (c * c)) hsq
    _ = a ^ (2 : ℕ) * t * (c * c) := by
            simp [pow_two, mul_assoc]
    _ = a ^ (2 : ℕ) * t * ‖c‖ ^ (2 : ℕ) := by
            -- rewrite RHS using `hcnorm`, avoid `simp` cancellation
            rw [hcnorm]

private lemma norm_mul_sq (a c : ℝ) :
    ‖a * c‖ ^ (2 : ℕ) = a ^ (2 : ℕ) * ‖c‖ ^ (2 : ℕ) := by
  have ha : |a| * |a| = a * a := by
    calc
      |a| * |a| = |a * a| := by
        simpa [abs_mul] using (abs_mul a a).symm
      _ = a * a := by
        simp [abs_of_nonneg (mul_self_nonneg a)]
  calc
    ‖a * c‖ ^ (2 : ℕ)
        = |a * c| ^ (2 : ℕ) := by
            simp [Real.norm_eq_abs]
    _ = (|a| * |c|) ^ (2 : ℕ) := by
            simp [abs_mul]
    _ = (|a| * |c|) * (|a| * |c|) := by
            simp [pow_two]
    _ = (|a| * |a|) * (|c| * |c|) := by
            ring_nf
    _ = (a * a) * (|c| * |c|) := by
            simp [ha]
    _ = a ^ (2 : ℕ) * ‖c‖ ^ (2 : ℕ) := by
            simp [pow_two, Real.norm_eq_abs, mul_assoc, mul_comm, mul_left_comm]

private lemma raise₀_injective : Function.Injective raise₀ := by
  intro n m hnm
  have h' : unpair₄ (raise₀ n) = unpair₄ (raise₀ m) := by
    simpa [hnm]
  -- Rewrite the decoded indices explicitly (avoid `simp` rewriting the equality away).
  rw [unpair₄_raise₀ (n := n)] at h'
  rw [unpair₄_raise₀ (n := m)] at h'
  have h1 : unpair₄₁ n = unpair₄₁ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) h'
    exact Nat.succ_injective this
  have h2 : unpair₄₂ n = unpair₄₂ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) h'
    simpa using this
  have h3 : unpair₄₃ n = unpair₄₃ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) h'
    simpa using this
  have h4 : unpair₄₄ n = unpair₄₄ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) h'
    simpa using this
  -- Recover `unpair₄ n = unpair₄ m`, hence `n = m`.
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  calc
    unpair₄ n = ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n)) := by
      simpa using (unpair₄_eta (n := n)).symm
    _ = ((unpair₄₁ m, unpair₄₂ m), (unpair₄₃ m, unpair₄₄ m)) := by
      simp [h1, h2, h3, h4]
    _ = unpair₄ m := by
      simpa using (unpair₄_eta (n := m))

private lemma raise₁_injective : Function.Injective raise₁ := by
  intro n m hnm
  have h' : unpair₄ (raise₁ n) = unpair₄ (raise₁ m) := by
    simpa [hnm]
  rw [unpair₄_raise₁ (n := n)] at h'
  rw [unpair₄_raise₁ (n := m)] at h'
  have h1 : unpair₄₁ n = unpair₄₁ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) h'
    simpa using this
  have h2 : unpair₄₂ n = unpair₄₂ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) h'
    exact Nat.succ_injective this
  have h3 : unpair₄₃ n = unpair₄₃ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) h'
    simpa using this
  have h4 : unpair₄₄ n = unpair₄₄ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) h'
    simpa using this
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  calc
    unpair₄ n = ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n)) := by
      simpa using (unpair₄_eta (n := n)).symm
    _ = ((unpair₄₁ m, unpair₄₂ m), (unpair₄₃ m, unpair₄₄ m)) := by
      simp [h1, h2, h3, h4]
    _ = unpair₄ m := by
      simpa using (unpair₄_eta (n := m))

private lemma raise₂_injective : Function.Injective raise₂ := by
  intro n m hnm
  have h' : unpair₄ (raise₂ n) = unpair₄ (raise₂ m) := by
    simpa [hnm]
  rw [unpair₄_raise₂ (n := n)] at h'
  rw [unpair₄_raise₂ (n := m)] at h'
  have h1 : unpair₄₁ n = unpair₄₁ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) h'
    simpa using this
  have h2 : unpair₄₂ n = unpair₄₂ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) h'
    simpa using this
  have h3 : unpair₄₃ n = unpair₄₃ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) h'
    exact Nat.succ_injective this
  have h4 : unpair₄₄ n = unpair₄₄ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) h'
    simpa using this
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  calc
    unpair₄ n = ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n)) := by
      simpa using (unpair₄_eta (n := n)).symm
    _ = ((unpair₄₁ m, unpair₄₂ m), (unpair₄₃ m, unpair₄₄ m)) := by
      simp [h1, h2, h3, h4]
    _ = unpair₄ m := by
      simpa using (unpair₄_eta (n := m))

private lemma raise₃_injective : Function.Injective raise₃ := by
  intro n m hnm
  have h' : unpair₄ (raise₃ n) = unpair₄ (raise₃ m) := by
    simpa [hnm]
  rw [unpair₄_raise₃ (n := n)] at h'
  rw [unpair₄_raise₃ (n := m)] at h'
  have h1 : unpair₄₁ n = unpair₄₁ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.1) h'
    simpa using this
  have h2 : unpair₄₂ n = unpair₄₂ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.1.2) h'
    simpa using this
  have h3 : unpair₄₃ n = unpair₄₃ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.1) h'
    simpa using this
  have h4 : unpair₄₄ n = unpair₄₄ m := by
    have := congrArg (fun p : (ℕ × ℕ) × (ℕ × ℕ) => p.2.2) h'
    exact Nat.succ_injective this
  refine (OSforGFF.RapidDecaySeqMulti.pairEquiv₄.symm.injective ?_)
  calc
    unpair₄ n = ((unpair₄₁ n, unpair₄₂ n), (unpair₄₃ n, unpair₄₄ n)) := by
      simpa using (unpair₄_eta (n := n)).symm
    _ = ((unpair₄₁ m, unpair₄₂ m), (unpair₄₃ m, unpair₄₄ m)) := by
      simp [h1, h2, h3, h4]
    _ = unpair₄ m := by
      simpa using (unpair₄_eta (n := m))

private lemma sqrt_two_mul_two_pow_sq (k : ℕ) :
    (Real.sqrt 2 * (2 : ℝ) ^ k) ^ (2 : ℕ) = (2 : ℝ) ^ (2 * k + 1) := by
  -- expand the square and collect powers of `2`
  simp [pow_two, mul_assoc, mul_left_comm, mul_comm,
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2), pow_add, pow_mul]

private lemma base₄_pow_raise₀_mul_two_unpair_le (k n : ℕ) :
    (base₄ (raise₀ n)) ^ (2 * k) * (2 * ((unpair₄₁ n + 1 : ℕ) : ℝ)) ≤
      ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2) := by
  have hbase : base₄ (raise₀ n) ≤ (2 : ℝ) * base₄ n :=
    base₄_raise₀_le_two_mul_base₄ (n := n)
  have hidx : ((unpair₄₁ n + 1 : ℕ) : ℝ) ≤ base₄ n := by
    simpa [Nat.cast_add_one] using (unpair₄₁_add_one_le_base₄ (n := n))
  have hbase0 : 0 ≤ base₄ (raise₀ n) :=
    (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := raise₀ n)).le
  have hb0 : 0 ≤ base₄ n :=
    (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := n)).le
  have hone : (1 : ℝ) ≤ base₄ n :=
    OSforGFF.RapidDecaySeqMulti.one_le_base₄ (n := n)
  have hpow : (base₄ (raise₀ n)) ^ (2 * k) ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) :=
    pow_le_pow_left₀ hbase0 hbase _
  have hidx2 : (2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * base₄ n := by
    exact mul_le_mul_of_nonneg_left hidx (by norm_num)
  have hnonneg_idx : 0 ≤ (2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ) := by positivity
  have hnonneg_pow : 0 ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) := by
    have : 0 ≤ (2 : ℝ) * base₄ n := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg this hb0
    exact pow_nonneg this _
  calc
    (base₄ (raise₀ n)) ^ (2 * k) * (2 * ((unpair₄₁ n + 1 : ℕ) : ℝ))
        ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) * (2 * ((unpair₄₁ n + 1 : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hpow hnonneg_idx
    _ ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) * ((2 : ℝ) * base₄ n) := by
            exact mul_le_mul_of_nonneg_left hidx2 hnonneg_pow
    _ = ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 1) := by
            rw [mul_pow]
            ring_nf
    _ ≤ ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2) := by
            have : (base₄ n) ^ (2 * k + 1) ≤ (base₄ n) ^ (2 * k + 2) := by
              exact pow_le_pow_right₀ hone (Nat.le_succ _)
            exact mul_le_mul_of_nonneg_left this (by positivity)

private lemma base₄_pow_raise₁_mul_two_unpair_le (k n : ℕ) :
    (base₄ (raise₁ n)) ^ (2 * k) * (2 * ((unpair₄₂ n + 1 : ℕ) : ℝ)) ≤
      ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2) := by
  have hbase : base₄ (raise₁ n) ≤ (2 : ℝ) * base₄ n :=
    base₄_raise₁_le_two_mul_base₄ (n := n)
  have hidx : ((unpair₄₂ n + 1 : ℕ) : ℝ) ≤ base₄ n := by
    simpa [Nat.cast_add_one] using (unpair₄₂_add_one_le_base₄ (n := n))
  have hbase0 : 0 ≤ base₄ (raise₁ n) :=
    (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := raise₁ n)).le
  have hb0 : 0 ≤ base₄ n :=
    (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := n)).le
  have hone : (1 : ℝ) ≤ base₄ n :=
    OSforGFF.RapidDecaySeqMulti.one_le_base₄ (n := n)
  have hpow : (base₄ (raise₁ n)) ^ (2 * k) ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) :=
    pow_le_pow_left₀ hbase0 hbase _
  have hidx2 : (2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * base₄ n := by
    exact mul_le_mul_of_nonneg_left hidx (by norm_num)
  have hnonneg_idx : 0 ≤ (2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ) := by positivity
  have hnonneg_pow : 0 ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) := by
    have : 0 ≤ (2 : ℝ) * base₄ n := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg this hb0
    exact pow_nonneg this _
  calc
    (base₄ (raise₁ n)) ^ (2 * k) * (2 * ((unpair₄₂ n + 1 : ℕ) : ℝ))
        ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) * (2 * ((unpair₄₂ n + 1 : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hpow hnonneg_idx
    _ ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) * ((2 : ℝ) * base₄ n) := by
            exact mul_le_mul_of_nonneg_left hidx2 hnonneg_pow
    _ = ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 1) := by
            rw [mul_pow]
            ring_nf
    _ ≤ ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2) := by
            have : (base₄ n) ^ (2 * k + 1) ≤ (base₄ n) ^ (2 * k + 2) := by
              exact pow_le_pow_right₀ hone (Nat.le_succ _)
            exact mul_le_mul_of_nonneg_left this (by positivity)

private lemma base₄_pow_raise₂_mul_two_unpair_le (k n : ℕ) :
    (base₄ (raise₂ n)) ^ (2 * k) * (2 * ((unpair₄₃ n + 1 : ℕ) : ℝ)) ≤
      ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2) := by
  have hbase : base₄ (raise₂ n) ≤ (2 : ℝ) * base₄ n :=
    base₄_raise₂_le_two_mul_base₄ (n := n)
  have hidx : ((unpair₄₃ n + 1 : ℕ) : ℝ) ≤ base₄ n := by
    simpa [Nat.cast_add_one] using (unpair₄₃_add_one_le_base₄ (n := n))
  have hbase0 : 0 ≤ base₄ (raise₂ n) :=
    (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := raise₂ n)).le
  have hb0 : 0 ≤ base₄ n :=
    (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := n)).le
  have hone : (1 : ℝ) ≤ base₄ n :=
    OSforGFF.RapidDecaySeqMulti.one_le_base₄ (n := n)
  have hpow : (base₄ (raise₂ n)) ^ (2 * k) ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) :=
    pow_le_pow_left₀ hbase0 hbase _
  have hidx2 : (2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * base₄ n := by
    exact mul_le_mul_of_nonneg_left hidx (by norm_num)
  have hnonneg_idx : 0 ≤ (2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ) := by positivity
  have hnonneg_pow : 0 ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) := by
    have : 0 ≤ (2 : ℝ) * base₄ n := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg this hb0
    exact pow_nonneg this _
  calc
    (base₄ (raise₂ n)) ^ (2 * k) * (2 * ((unpair₄₃ n + 1 : ℕ) : ℝ))
        ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) * (2 * ((unpair₄₃ n + 1 : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hpow hnonneg_idx
    _ ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) * ((2 : ℝ) * base₄ n) := by
            exact mul_le_mul_of_nonneg_left hidx2 hnonneg_pow
    _ = ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 1) := by
            rw [mul_pow]
            ring_nf
    _ ≤ ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2) := by
            have : (base₄ n) ^ (2 * k + 1) ≤ (base₄ n) ^ (2 * k + 2) := by
              exact pow_le_pow_right₀ hone (Nat.le_succ _)
            exact mul_le_mul_of_nonneg_left this (by positivity)

private lemma base₄_pow_raise₃_mul_two_unpair_le (k n : ℕ) :
    (base₄ (raise₃ n)) ^ (2 * k) * (2 * ((unpair₄₄ n + 1 : ℕ) : ℝ)) ≤
      ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2) := by
  have hbase : base₄ (raise₃ n) ≤ (2 : ℝ) * base₄ n :=
    base₄_raise₃_le_two_mul_base₄ (n := n)
  have hidx : ((unpair₄₄ n + 1 : ℕ) : ℝ) ≤ base₄ n := by
    simpa [Nat.cast_add_one] using (unpair₄₄_add_one_le_base₄ (n := n))
  have hbase0 : 0 ≤ base₄ (raise₃ n) :=
    (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := raise₃ n)).le
  have hb0 : 0 ≤ base₄ n :=
    (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := n)).le
  have hone : (1 : ℝ) ≤ base₄ n :=
    OSforGFF.RapidDecaySeqMulti.one_le_base₄ (n := n)
  have hpow : (base₄ (raise₃ n)) ^ (2 * k) ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) :=
    pow_le_pow_left₀ hbase0 hbase _
  have hidx2 : (2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * base₄ n := by
    exact mul_le_mul_of_nonneg_left hidx (by norm_num)
  have hnonneg_idx : 0 ≤ (2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ) := by positivity
  have hnonneg_pow : 0 ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) := by
    have : 0 ≤ (2 : ℝ) * base₄ n := by
      have : 0 ≤ (2 : ℝ) := by norm_num
      exact mul_nonneg this hb0
    exact pow_nonneg this _
  calc
    (base₄ (raise₃ n)) ^ (2 * k) * (2 * ((unpair₄₄ n + 1 : ℕ) : ℝ))
        ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) * (2 * ((unpair₄₄ n + 1 : ℕ) : ℝ)) := by
            exact mul_le_mul_of_nonneg_right hpow hnonneg_idx
    _ ≤ ((2 : ℝ) * base₄ n) ^ (2 * k) * ((2 : ℝ) * base₄ n) := by
            exact mul_le_mul_of_nonneg_left hidx2 hnonneg_pow
    _ = ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 1) := by
            rw [mul_pow]
            ring_nf
    _ ≤ ((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2) := by
            have : (base₄ n) ^ (2 * k + 1) ≤ (base₄ n) ^ (2 * k + 2) := by
              exact pow_le_pow_right₀ hone (Nat.le_succ _)
            exact mul_le_mul_of_nonneg_left this (by positivity)

/-! ## Coefficient seminorm shift: `raiseOpCLM` (coordinate 0) -/

lemma coeffSeminormSeq_raiseOpCLM0_le (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (raiseOpCLM ξ (0 : Fin STDimension) f) ≤
      (Real.sqrt 2 * (2 : ℝ) ^ k) * coeffSeminormSeq ξ hξ (k + 1) f := by
  classical
  let A : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) k
      (normalizedCoeffRapidDecay ξ hξ (raiseOpCLM ξ (0 : Fin STDimension) f))
  let B : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) (k + 1) (normalizedCoeffRapidDecay ξ hξ f)
  let C0 : ℝ := Real.sqrt 2 * (2 : ℝ) ^ k
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  have hC : 0 ≤ C0 * ‖B‖ := by
    dsimp [C0]
    positivity
  have hAB : ‖A‖ ≤ C0 * ‖B‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := C0 * ‖B‖) hC ?_
    intro s
    -- work with squares (`p = 2`)
    have hsq :
        (∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ)) ≤ (C0 * ‖B‖) ^ (2 : ℕ) := by
      let g : ℕ → ℝ := fun n => ‖(A : ℕ → ℝ) n‖ ^ (2 : ℕ)

      have hg0 : ∀ x ∈ s, x ∉ Set.range raise₀ → g x = 0 := by
        intro x hx hxnot
        have hx0 : unpair₄₁ x = 0 := by
          by_contra hne
          have hpos : 0 < unpair₄₁ x := Nat.pos_of_ne_zero hne
          have : x ∈ Set.range raise₀ := by
            refine ⟨lower₀ x, ?_⟩
            simpa using (raise₀_lower₀_of_pos (n := x) hpos)
          exact hxnot this
        have hcoeff :
            normalizedCoeffCLM_SpaceTime ξ hξ x (raiseOpCLM ξ (0 : Fin STDimension) f) = 0 := by
          rw [normalizedCoeffCLM_SpaceTime_raiseOpCLM0 (ξ := ξ) (hξ := hξ) (n := x) (f := f)]
          simp [hx0]
        have hAx :
            (A : ℕ → ℝ) x =
              (base₄ x) ^ k *
                normalizedCoeffCLM_SpaceTime ξ hξ x (raiseOpCLM ξ (0 : Fin STDimension) f) := by
          simpa [A] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
              (f := raiseOpCLM ξ (0 : Fin STDimension) f) (n := x))
        have hAx0 : (A : ℕ → ℝ) x = 0 := by
          rw [hAx, hcoeff]
          simp
        simp [g, hAx0]

      have hinj : Set.InjOn raise₀ (raise₀ ⁻¹' (↑s : Set ℕ)) :=
        Set.injOn_of_injective raise₀_injective

      have hsum :
          (∑ y ∈ s, g y) = ∑ n ∈ s.preimage raise₀ hinj, g (raise₀ n) := by
        simpa using
          (Finset.sum_preimage (f := raise₀) (s := s) hinj (g := g) hg0).symm

      have hpoint :
          ∀ n, g (raise₀ n) ≤ ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
        intro n
        set c : ℝ := normalizedCoeffCLM_SpaceTime ξ hξ n f

        have hAcoord :
            (A : ℕ → ℝ) (raise₀ n) =
              (base₄ (raise₀ n)) ^ k *
                Real.sqrt ((2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ)) * c := by
          have hcoord :
              (A : ℕ → ℝ) (raise₀ n) =
                (base₄ (raise₀ n)) ^ k *
                  normalizedCoeffCLM_SpaceTime ξ hξ (raise₀ n)
                    (raiseOpCLM ξ (0 : Fin STDimension) f) := by
            simpa [A] using
              (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
                (f := raiseOpCLM ξ (0 : Fin STDimension) f) (n := raise₀ n))
          rw [hcoord,
            normalizedCoeffCLM_SpaceTime_raiseOpCLM0_raise₀ (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
          simp [c, mul_assoc]

        have ht0 : 0 ≤ (2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ) := by positivity
        have hg :
            g (raise₀ n) =
              ((base₄ (raise₀ n)) ^ k) ^ (2 : ℕ) *
                ((2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          dsimp [g]
          -- rewrite `A` at the raised index, then apply the scalar norm identity
          rw [hAcoord]
          exact
            norm_mul_sqrt_mul_sq (a := (base₄ (raise₀ n)) ^ k)
              (t := (2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ)) (c := c) ht0

        have hpowA :
            ((base₄ (raise₀ n)) ^ k) ^ (2 : ℕ) = (base₄ (raise₀ n)) ^ (2 * k) := by
          calc
            ((base₄ (raise₀ n)) ^ k) ^ (2 : ℕ) = (base₄ (raise₀ n)) ^ (k * 2) := by
              simp [pow_mul]
            _ = (base₄ (raise₀ n)) ^ (2 * k) := by
              simp [Nat.mul_comm]

        have hBcoord :
            (B : ℕ → ℝ) n = (base₄ n) ^ (k + 1) * c := by
          simpa [B, c] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k + 1) (f := f) (n := n))

        have hBn :
            ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) = ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hBcoord, mul_assoc] using (norm_mul_sq (a := (base₄ n) ^ (k + 1)) (c := c))

        have hpowB :
            ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) = (base₄ n) ^ (2 * k + 2) := by
          calc
            ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) = (base₄ n) ^ ((k + 1) * 2) := by
              simp [pow_mul]
            _ = (base₄ n) ^ (2 * k + 2) := by
              have hk : (k + 1) * 2 = 2 * k + 2 := by
                calc
                  (k + 1) * 2 = k * 2 + 2 := by
                    simpa [Nat.succ_mul]
                  _ = 2 * k + 2 := by
                    simp [Nat.mul_comm]
              simpa [hk]

        have hBn2 :
            ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) = (base₄ n) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hpowB, mul_assoc] using hBn

        have hc2 : 0 ≤ ‖c‖ ^ (2 : ℕ) := by positivity

        -- now use the explicit expression for `g (raise₀ n)`
        have hg' :
            g (raise₀ n) =
              (base₄ (raise₀ n)) ^ (2 * k) * (2 * ((unpair₄₁ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hg, hpowA, mul_assoc] using hg

        -- Multiply the scalar weight inequality by `‖c‖^2`, then rewrite the RHS using `hBn2`.
        have hmul :=
          mul_le_mul_of_nonneg_right (base₄_pow_raise₀_mul_two_unpair_le (k := k) (n := n)) hc2

        have hrhs :
            (((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2)) * ‖c‖ ^ (2 : ℕ) =
              ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
          calc
            (((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2)) * ‖c‖ ^ (2 : ℕ)
                = ((2 : ℝ) ^ (2 * k + 1)) * ((base₄ n) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)) := by
                    exact (mul_assoc ((2 : ℝ) ^ (2 * k + 1)) ((base₄ n) ^ (2 * k + 2)) (‖c‖ ^ (2 : ℕ)))
            _ = ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
                    rw [hBn2.symm]

        have hmul2 := hmul
        rw [hrhs] at hmul2

        rw [hg']
        exact hmul2

      calc
        ∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ) = ∑ i ∈ s, g i := by
          simp [g]
        _ = ∑ n ∈ s.preimage raise₀ hinj, g (raise₀ n) := hsum
        _ ≤ ∑ n ∈ s.preimage raise₀ hinj,
              ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
            exact Finset.sum_le_sum fun n hn => hpoint n
        _ = ((2 : ℝ) ^ (2 * k + 1)) *
              ∑ n ∈ s.preimage raise₀ hinj, ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
            simpa using
              (Finset.mul_sum (a := (2 : ℝ) ^ (2 * k + 1)) (s := s.preimage raise₀ hinj)
                (f := fun n => ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ))).symm
        _ ≤ ((2 : ℝ) ^ (2 * k + 1)) * ‖B‖ ^ (2 : ℕ) := by
            have hBsum :
                (∑ n ∈ s.preimage raise₀ hinj, ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ)) ≤ ‖B‖ ^ (2 : ℕ) := by
              simpa using
                (lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) hp B (s.preimage raise₀ hinj))
            have hnonneg : 0 ≤ (2 : ℝ) ^ (2 * k + 1) := by positivity
            exact mul_le_mul_of_nonneg_left hBsum hnonneg
        _ = (C0 * ‖B‖) ^ (2 : ℕ) := by
            have hC0sq : C0 ^ (2 : ℕ) = (2 : ℝ) ^ (2 * k + 1) := by
              simpa [C0] using (sqrt_two_mul_two_pow_sq (k := k))
            calc
              ((2 : ℝ) ^ (2 * k + 1)) * ‖B‖ ^ (2 : ℕ)
                  = (C0 ^ (2 : ℕ)) * ‖B‖ ^ (2 : ℕ) := by
                      simpa [hC0sq]
              _ = (C0 * ‖B‖) ^ (2 : ℕ) := by
                      simpa [mul_pow] using (mul_pow C0 ‖B‖ (2 : ℕ)).symm

    -- convert back to `‖·‖ ^ (p.toReal)` with `p = 2`
    simpa using hsq

  -- rewrite back to the coefficient seminorms
  simpa [coeffSeminormSeq_apply_eq_norm, A, B, C0] using hAB

/-! ## Coefficient seminorm shift: `raiseOpCLM` (coordinate 1) -/

lemma coeffSeminormSeq_raiseOpCLM1_le (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (raiseOpCLM ξ (1 : Fin STDimension) f) ≤
      (Real.sqrt 2 * (2 : ℝ) ^ k) * coeffSeminormSeq ξ hξ (k + 1) f := by
  classical
  let A : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) k
      (normalizedCoeffRapidDecay ξ hξ (raiseOpCLM ξ (1 : Fin STDimension) f))
  let B : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) (k + 1) (normalizedCoeffRapidDecay ξ hξ f)
  let C0 : ℝ := Real.sqrt 2 * (2 : ℝ) ^ k
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  have hC : 0 ≤ C0 * ‖B‖ := by
    dsimp [C0]
    positivity
  have hAB : ‖A‖ ≤ C0 * ‖B‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := C0 * ‖B‖) hC ?_
    intro s
    have hsq :
        (∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ)) ≤ (C0 * ‖B‖) ^ (2 : ℕ) := by
      let g : ℕ → ℝ := fun n => ‖(A : ℕ → ℝ) n‖ ^ (2 : ℕ)

      have hg0 : ∀ x ∈ s, x ∉ Set.range raise₁ → g x = 0 := by
        intro x hx hxnot
        have hx0 : unpair₄₂ x = 0 := by
          by_contra hne
          have hpos : 0 < unpair₄₂ x := Nat.pos_of_ne_zero hne
          have : x ∈ Set.range raise₁ := by
            refine ⟨lower₁ x, ?_⟩
            simpa using (raise₁_lower₁_of_pos (n := x) hpos)
          exact hxnot this
        have hcoeff :
            normalizedCoeffCLM_SpaceTime ξ hξ x (raiseOpCLM ξ (1 : Fin STDimension) f) = 0 := by
          rw [normalizedCoeffCLM_SpaceTime_raiseOpCLM1 (ξ := ξ) (hξ := hξ) (n := x) (f := f)]
          simp [hx0]
        have hAx :
            (A : ℕ → ℝ) x =
              (base₄ x) ^ k *
                normalizedCoeffCLM_SpaceTime ξ hξ x (raiseOpCLM ξ (1 : Fin STDimension) f) := by
          simpa [A] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
              (f := raiseOpCLM ξ (1 : Fin STDimension) f) (n := x))
        have hAx0 : (A : ℕ → ℝ) x = 0 := by
          rw [hAx, hcoeff]
          simp
        simp [g, hAx0]

      have hinj : Set.InjOn raise₁ (raise₁ ⁻¹' (↑s : Set ℕ)) :=
        Set.injOn_of_injective raise₁_injective

      have hsum :
          (∑ y ∈ s, g y) = ∑ n ∈ s.preimage raise₁ hinj, g (raise₁ n) := by
        simpa using
          (Finset.sum_preimage (f := raise₁) (s := s) hinj (g := g) hg0).symm

      have hpoint :
          ∀ n, g (raise₁ n) ≤ ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
        intro n
        set c : ℝ := normalizedCoeffCLM_SpaceTime ξ hξ n f

        have hAcoord :
            (A : ℕ → ℝ) (raise₁ n) =
              (base₄ (raise₁ n)) ^ k *
                Real.sqrt ((2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ)) * c := by
          have hcoord :
              (A : ℕ → ℝ) (raise₁ n) =
                (base₄ (raise₁ n)) ^ k *
                  normalizedCoeffCLM_SpaceTime ξ hξ (raise₁ n)
                    (raiseOpCLM ξ (1 : Fin STDimension) f) := by
            simpa [A] using
              (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
                (f := raiseOpCLM ξ (1 : Fin STDimension) f) (n := raise₁ n))
          rw [hcoord,
            normalizedCoeffCLM_SpaceTime_raiseOpCLM1_raise₁ (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
          simp [c, mul_assoc]

        have ht0 : 0 ≤ (2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ) := by positivity
        have hg :
            g (raise₁ n) =
              ((base₄ (raise₁ n)) ^ k) ^ (2 : ℕ) *
                ((2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          dsimp [g]
          rw [hAcoord]
          exact
            norm_mul_sqrt_mul_sq (a := (base₄ (raise₁ n)) ^ k)
              (t := (2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ)) (c := c) ht0

        have hpowA :
            ((base₄ (raise₁ n)) ^ k) ^ (2 : ℕ) = (base₄ (raise₁ n)) ^ (2 * k) := by
          calc
            ((base₄ (raise₁ n)) ^ k) ^ (2 : ℕ) = (base₄ (raise₁ n)) ^ (k * 2) := by
              simp [pow_mul]
            _ = (base₄ (raise₁ n)) ^ (2 * k) := by
              simp [Nat.mul_comm]

        have hBcoord :
            (B : ℕ → ℝ) n = (base₄ n) ^ (k + 1) * c := by
          simpa [B, c] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k + 1) (f := f) (n := n))

        have hBn :
            ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) = ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hBcoord, mul_assoc] using (norm_mul_sq (a := (base₄ n) ^ (k + 1)) (c := c))

        have hpowB :
            ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) = (base₄ n) ^ (2 * k + 2) := by
          calc
            ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) = (base₄ n) ^ ((k + 1) * 2) := by
              simp [pow_mul]
            _ = (base₄ n) ^ (2 * k + 2) := by
              have hk : (k + 1) * 2 = 2 * k + 2 := by
                calc
                  (k + 1) * 2 = k * 2 + 2 := by
                    simpa [Nat.succ_mul]
                  _ = 2 * k + 2 := by
                    simp [Nat.mul_comm]
              simpa [hk]

        have hBn2 :
            ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) = (base₄ n) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hpowB, mul_assoc] using hBn

        have hc2 : 0 ≤ ‖c‖ ^ (2 : ℕ) := by positivity

        have hg' :
            g (raise₁ n) =
              (base₄ (raise₁ n)) ^ (2 * k) * (2 * ((unpair₄₂ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hg, hpowA, mul_assoc] using hg

        have hmul :=
          mul_le_mul_of_nonneg_right (base₄_pow_raise₁_mul_two_unpair_le (k := k) (n := n)) hc2

        have hrhs :
            (((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2)) * ‖c‖ ^ (2 : ℕ) =
              ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
          calc
            (((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2)) * ‖c‖ ^ (2 : ℕ)
                = ((2 : ℝ) ^ (2 * k + 1)) * ((base₄ n) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)) := by
                    exact (mul_assoc ((2 : ℝ) ^ (2 * k + 1)) ((base₄ n) ^ (2 * k + 2)) (‖c‖ ^ (2 : ℕ)))
            _ = ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
                    rw [hBn2.symm]

        have hmul2 := hmul
        rw [hrhs] at hmul2

        rw [hg']
        exact hmul2

      calc
        ∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ) = ∑ i ∈ s, g i := by
          simp [g]
        _ = ∑ n ∈ s.preimage raise₁ hinj, g (raise₁ n) := hsum
        _ ≤ ∑ n ∈ s.preimage raise₁ hinj,
              ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
            exact Finset.sum_le_sum fun n hn => hpoint n
        _ = ((2 : ℝ) ^ (2 * k + 1)) *
              ∑ n ∈ s.preimage raise₁ hinj, ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
            simpa using
              (Finset.mul_sum (a := (2 : ℝ) ^ (2 * k + 1)) (s := s.preimage raise₁ hinj)
                (f := fun n => ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ))).symm
        _ ≤ ((2 : ℝ) ^ (2 * k + 1)) * ‖B‖ ^ (2 : ℕ) := by
            have hBsum :
                (∑ n ∈ s.preimage raise₁ hinj, ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ)) ≤ ‖B‖ ^ (2 : ℕ) := by
              simpa using
                (lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) hp B (s.preimage raise₁ hinj))
            have hnonneg : 0 ≤ (2 : ℝ) ^ (2 * k + 1) := by positivity
            exact mul_le_mul_of_nonneg_left hBsum hnonneg
        _ = (C0 * ‖B‖) ^ (2 : ℕ) := by
            have hC0sq : C0 ^ (2 : ℕ) = (2 : ℝ) ^ (2 * k + 1) := by
              simpa [C0] using (sqrt_two_mul_two_pow_sq (k := k))
            calc
              ((2 : ℝ) ^ (2 * k + 1)) * ‖B‖ ^ (2 : ℕ)
                  = (C0 ^ (2 : ℕ)) * ‖B‖ ^ (2 : ℕ) := by
                      simpa [hC0sq]
              _ = (C0 * ‖B‖) ^ (2 : ℕ) := by
                      simpa [mul_pow] using (mul_pow C0 ‖B‖ (2 : ℕ)).symm

    simpa using hsq

  simpa [coeffSeminormSeq_apply_eq_norm, A, B, C0] using hAB

/-! ## Coefficient seminorm shift: `raiseOpCLM` (coordinate 2) -/

lemma coeffSeminormSeq_raiseOpCLM2_le (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (raiseOpCLM ξ (2 : Fin STDimension) f) ≤
      (Real.sqrt 2 * (2 : ℝ) ^ k) * coeffSeminormSeq ξ hξ (k + 1) f := by
  classical
  let A : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) k
      (normalizedCoeffRapidDecay ξ hξ (raiseOpCLM ξ (2 : Fin STDimension) f))
  let B : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) (k + 1) (normalizedCoeffRapidDecay ξ hξ f)
  let C0 : ℝ := Real.sqrt 2 * (2 : ℝ) ^ k
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  have hC : 0 ≤ C0 * ‖B‖ := by
    dsimp [C0]
    positivity
  have hAB : ‖A‖ ≤ C0 * ‖B‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := C0 * ‖B‖) hC ?_
    intro s
    have hsq :
        (∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ)) ≤ (C0 * ‖B‖) ^ (2 : ℕ) := by
      let g : ℕ → ℝ := fun n => ‖(A : ℕ → ℝ) n‖ ^ (2 : ℕ)

      have hg0 : ∀ x ∈ s, x ∉ Set.range raise₂ → g x = 0 := by
        intro x hx hxnot
        have hx0 : unpair₄₃ x = 0 := by
          by_contra hne
          have hpos : 0 < unpair₄₃ x := Nat.pos_of_ne_zero hne
          have : x ∈ Set.range raise₂ := by
            refine ⟨lower₂ x, ?_⟩
            simpa using (raise₂_lower₂_of_pos (n := x) hpos)
          exact hxnot this
        have hcoeff :
            normalizedCoeffCLM_SpaceTime ξ hξ x (raiseOpCLM ξ (2 : Fin STDimension) f) = 0 := by
          rw [normalizedCoeffCLM_SpaceTime_raiseOpCLM2 (ξ := ξ) (hξ := hξ) (n := x) (f := f)]
          simp [hx0]
        have hAx :
            (A : ℕ → ℝ) x =
              (base₄ x) ^ k *
                normalizedCoeffCLM_SpaceTime ξ hξ x (raiseOpCLM ξ (2 : Fin STDimension) f) := by
          simpa [A] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
              (f := raiseOpCLM ξ (2 : Fin STDimension) f) (n := x))
        have hAx0 : (A : ℕ → ℝ) x = 0 := by
          rw [hAx, hcoeff]
          simp
        simp [g, hAx0]

      have hinj : Set.InjOn raise₂ (raise₂ ⁻¹' (↑s : Set ℕ)) :=
        Set.injOn_of_injective raise₂_injective

      have hsum :
          (∑ y ∈ s, g y) = ∑ n ∈ s.preimage raise₂ hinj, g (raise₂ n) := by
        simpa using
          (Finset.sum_preimage (f := raise₂) (s := s) hinj (g := g) hg0).symm

      have hpoint :
          ∀ n, g (raise₂ n) ≤ ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
        intro n
        set c : ℝ := normalizedCoeffCLM_SpaceTime ξ hξ n f

        have hAcoord :
            (A : ℕ → ℝ) (raise₂ n) =
              (base₄ (raise₂ n)) ^ k *
                Real.sqrt ((2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ)) * c := by
          have hcoord :
              (A : ℕ → ℝ) (raise₂ n) =
                (base₄ (raise₂ n)) ^ k *
                  normalizedCoeffCLM_SpaceTime ξ hξ (raise₂ n)
                    (raiseOpCLM ξ (2 : Fin STDimension) f) := by
            simpa [A] using
              (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
                (f := raiseOpCLM ξ (2 : Fin STDimension) f) (n := raise₂ n))
          rw [hcoord,
            normalizedCoeffCLM_SpaceTime_raiseOpCLM2_raise₂ (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
          simp [c, mul_assoc]

        have ht0 : 0 ≤ (2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ) := by positivity
        have hg :
            g (raise₂ n) =
              ((base₄ (raise₂ n)) ^ k) ^ (2 : ℕ) *
                ((2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          dsimp [g]
          rw [hAcoord]
          exact
            norm_mul_sqrt_mul_sq (a := (base₄ (raise₂ n)) ^ k)
              (t := (2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ)) (c := c) ht0

        have hpowA :
            ((base₄ (raise₂ n)) ^ k) ^ (2 : ℕ) = (base₄ (raise₂ n)) ^ (2 * k) := by
          calc
            ((base₄ (raise₂ n)) ^ k) ^ (2 : ℕ) = (base₄ (raise₂ n)) ^ (k * 2) := by
              simp [pow_mul]
            _ = (base₄ (raise₂ n)) ^ (2 * k) := by
              simp [Nat.mul_comm]

        have hBcoord :
            (B : ℕ → ℝ) n = (base₄ n) ^ (k + 1) * c := by
          simpa [B, c] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k + 1) (f := f) (n := n))

        have hBn :
            ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) = ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hBcoord, mul_assoc] using (norm_mul_sq (a := (base₄ n) ^ (k + 1)) (c := c))

        have hpowB :
            ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) = (base₄ n) ^ (2 * k + 2) := by
          calc
            ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) = (base₄ n) ^ ((k + 1) * 2) := by
              simp [pow_mul]
            _ = (base₄ n) ^ (2 * k + 2) := by
              have hk : (k + 1) * 2 = 2 * k + 2 := by
                calc
                  (k + 1) * 2 = k * 2 + 2 := by
                    simpa [Nat.succ_mul]
                  _ = 2 * k + 2 := by
                    simp [Nat.mul_comm]
              simpa [hk]

        have hBn2 :
            ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) = (base₄ n) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hpowB, mul_assoc] using hBn

        have hc2 : 0 ≤ ‖c‖ ^ (2 : ℕ) := by positivity

        have hg' :
            g (raise₂ n) =
              (base₄ (raise₂ n)) ^ (2 * k) * (2 * ((unpair₄₃ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hg, hpowA, mul_assoc] using hg

        have hmul :=
          mul_le_mul_of_nonneg_right (base₄_pow_raise₂_mul_two_unpair_le (k := k) (n := n)) hc2

        have hrhs :
            (((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2)) * ‖c‖ ^ (2 : ℕ) =
              ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
          calc
            (((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2)) * ‖c‖ ^ (2 : ℕ)
                = ((2 : ℝ) ^ (2 * k + 1)) * ((base₄ n) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)) := by
                    exact (mul_assoc ((2 : ℝ) ^ (2 * k + 1)) ((base₄ n) ^ (2 * k + 2)) (‖c‖ ^ (2 : ℕ)))
            _ = ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
                    rw [hBn2.symm]

        have hmul2 := hmul
        rw [hrhs] at hmul2

        rw [hg']
        exact hmul2

      calc
        ∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ) = ∑ i ∈ s, g i := by
          simp [g]
        _ = ∑ n ∈ s.preimage raise₂ hinj, g (raise₂ n) := hsum
        _ ≤ ∑ n ∈ s.preimage raise₂ hinj,
              ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
            exact Finset.sum_le_sum fun n hn => hpoint n
        _ = ((2 : ℝ) ^ (2 * k + 1)) *
              ∑ n ∈ s.preimage raise₂ hinj, ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
            simpa using
              (Finset.mul_sum (a := (2 : ℝ) ^ (2 * k + 1)) (s := s.preimage raise₂ hinj)
                (f := fun n => ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ))).symm
        _ ≤ ((2 : ℝ) ^ (2 * k + 1)) * ‖B‖ ^ (2 : ℕ) := by
            have hBsum :
                (∑ n ∈ s.preimage raise₂ hinj, ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ)) ≤ ‖B‖ ^ (2 : ℕ) := by
              simpa using
                (lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) hp B (s.preimage raise₂ hinj))
            have hnonneg : 0 ≤ (2 : ℝ) ^ (2 * k + 1) := by positivity
            exact mul_le_mul_of_nonneg_left hBsum hnonneg
        _ = (C0 * ‖B‖) ^ (2 : ℕ) := by
            have hC0sq : C0 ^ (2 : ℕ) = (2 : ℝ) ^ (2 * k + 1) := by
              simpa [C0] using (sqrt_two_mul_two_pow_sq (k := k))
            calc
              ((2 : ℝ) ^ (2 * k + 1)) * ‖B‖ ^ (2 : ℕ)
                  = (C0 ^ (2 : ℕ)) * ‖B‖ ^ (2 : ℕ) := by
                      simpa [hC0sq]
              _ = (C0 * ‖B‖) ^ (2 : ℕ) := by
                      simpa [mul_pow] using (mul_pow C0 ‖B‖ (2 : ℕ)).symm

    simpa using hsq

  simpa [coeffSeminormSeq_apply_eq_norm, A, B, C0] using hAB

/-! ## Coefficient seminorm shift: `raiseOpCLM` (coordinate 3) -/

lemma coeffSeminormSeq_raiseOpCLM3_le (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (raiseOpCLM ξ (3 : Fin STDimension) f) ≤
      (Real.sqrt 2 * (2 : ℝ) ^ k) * coeffSeminormSeq ξ hξ (k + 1) f := by
  classical
  let A : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) k
      (normalizedCoeffRapidDecay ξ hξ (raiseOpCLM ξ (3 : Fin STDimension) f))
  let B : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) (k + 1) (normalizedCoeffRapidDecay ξ hξ f)
  let C0 : ℝ := Real.sqrt 2 * (2 : ℝ) ^ k
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  have hC : 0 ≤ C0 * ‖B‖ := by
    dsimp [C0]
    positivity
  have hAB : ‖A‖ ≤ C0 * ‖B‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := C0 * ‖B‖) hC ?_
    intro s
    have hsq :
        (∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ)) ≤ (C0 * ‖B‖) ^ (2 : ℕ) := by
      let g : ℕ → ℝ := fun n => ‖(A : ℕ → ℝ) n‖ ^ (2 : ℕ)

      have hg0 : ∀ x ∈ s, x ∉ Set.range raise₃ → g x = 0 := by
        intro x hx hxnot
        have hx0 : unpair₄₄ x = 0 := by
          by_contra hne
          have hpos : 0 < unpair₄₄ x := Nat.pos_of_ne_zero hne
          have : x ∈ Set.range raise₃ := by
            refine ⟨lower₃ x, ?_⟩
            simpa using (raise₃_lower₃_of_pos (n := x) hpos)
          exact hxnot this
        have hcoeff :
            normalizedCoeffCLM_SpaceTime ξ hξ x (raiseOpCLM ξ (3 : Fin STDimension) f) = 0 := by
          rw [normalizedCoeffCLM_SpaceTime_raiseOpCLM3 (ξ := ξ) (hξ := hξ) (n := x) (f := f)]
          simp [hx0]
        have hAx :
            (A : ℕ → ℝ) x =
              (base₄ x) ^ k *
                normalizedCoeffCLM_SpaceTime ξ hξ x (raiseOpCLM ξ (3 : Fin STDimension) f) := by
          simpa [A] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
              (f := raiseOpCLM ξ (3 : Fin STDimension) f) (n := x))
        have hAx0 : (A : ℕ → ℝ) x = 0 := by
          rw [hAx, hcoeff]
          simp
        simp [g, hAx0]

      have hinj : Set.InjOn raise₃ (raise₃ ⁻¹' (↑s : Set ℕ)) :=
        Set.injOn_of_injective raise₃_injective

      have hsum :
          (∑ y ∈ s, g y) = ∑ n ∈ s.preimage raise₃ hinj, g (raise₃ n) := by
        simpa using
          (Finset.sum_preimage (f := raise₃) (s := s) hinj (g := g) hg0).symm

      have hpoint :
          ∀ n, g (raise₃ n) ≤ ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
        intro n
        set c : ℝ := normalizedCoeffCLM_SpaceTime ξ hξ n f

        have hAcoord :
            (A : ℕ → ℝ) (raise₃ n) =
              (base₄ (raise₃ n)) ^ k *
                Real.sqrt ((2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ)) * c := by
          have hcoord :
              (A : ℕ → ℝ) (raise₃ n) =
                (base₄ (raise₃ n)) ^ k *
                  normalizedCoeffCLM_SpaceTime ξ hξ (raise₃ n)
                    (raiseOpCLM ξ (3 : Fin STDimension) f) := by
            simpa [A] using
              (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
                (f := raiseOpCLM ξ (3 : Fin STDimension) f) (n := raise₃ n))
          rw [hcoord,
            normalizedCoeffCLM_SpaceTime_raiseOpCLM3_raise₃ (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
          simp [c, mul_assoc]

        have ht0 : 0 ≤ (2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ) := by positivity
        have hg :
            g (raise₃ n) =
              ((base₄ (raise₃ n)) ^ k) ^ (2 : ℕ) *
                ((2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          dsimp [g]
          rw [hAcoord]
          exact
            norm_mul_sqrt_mul_sq (a := (base₄ (raise₃ n)) ^ k)
              (t := (2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ)) (c := c) ht0

        have hpowA :
            ((base₄ (raise₃ n)) ^ k) ^ (2 : ℕ) = (base₄ (raise₃ n)) ^ (2 * k) := by
          calc
            ((base₄ (raise₃ n)) ^ k) ^ (2 : ℕ) = (base₄ (raise₃ n)) ^ (k * 2) := by
              simp [pow_mul]
            _ = (base₄ (raise₃ n)) ^ (2 * k) := by
              simp [Nat.mul_comm]

        have hBcoord :
            (B : ℕ → ℝ) n = (base₄ n) ^ (k + 1) * c := by
          simpa [B, c] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k + 1) (f := f) (n := n))

        have hBn :
            ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) = ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hBcoord, mul_assoc] using (norm_mul_sq (a := (base₄ n) ^ (k + 1)) (c := c))

        have hpowB :
            ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) = (base₄ n) ^ (2 * k + 2) := by
          calc
            ((base₄ n) ^ (k + 1)) ^ (2 : ℕ) = (base₄ n) ^ ((k + 1) * 2) := by
              simp [pow_mul]
            _ = (base₄ n) ^ (2 * k + 2) := by
              have hk : (k + 1) * 2 = 2 * k + 2 := by
                calc
                  (k + 1) * 2 = k * 2 + 2 := by
                    simpa [Nat.succ_mul]
                  _ = 2 * k + 2 := by
                    simp [Nat.mul_comm]
              simpa [hk]

        have hBn2 :
            ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) = (base₄ n) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hpowB, mul_assoc] using hBn

        have hc2 : 0 ≤ ‖c‖ ^ (2 : ℕ) := by positivity

        have hg' :
            g (raise₃ n) =
              (base₄ (raise₃ n)) ^ (2 * k) * (2 * ((unpair₄₄ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hg, hpowA, mul_assoc] using hg

        have hmul :=
          mul_le_mul_of_nonneg_right (base₄_pow_raise₃_mul_two_unpair_le (k := k) (n := n)) hc2

        have hrhs :
            (((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2)) * ‖c‖ ^ (2 : ℕ) =
              ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
          calc
            (((2 : ℝ) ^ (2 * k + 1)) * (base₄ n) ^ (2 * k + 2)) * ‖c‖ ^ (2 : ℕ)
                = ((2 : ℝ) ^ (2 * k + 1)) * ((base₄ n) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)) := by
                    exact (mul_assoc ((2 : ℝ) ^ (2 * k + 1)) ((base₄ n) ^ (2 * k + 2)) (‖c‖ ^ (2 : ℕ)))
            _ = ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
                    rw [hBn2.symm]

        have hmul2 := hmul
        rw [hrhs] at hmul2

        rw [hg']
        exact hmul2

      calc
        ∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ) = ∑ i ∈ s, g i := by
          simp [g]
        _ = ∑ n ∈ s.preimage raise₃ hinj, g (raise₃ n) := hsum
        _ ≤ ∑ n ∈ s.preimage raise₃ hinj,
              ((2 : ℝ) ^ (2 * k + 1)) * ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
            exact Finset.sum_le_sum fun n hn => hpoint n
        _ = ((2 : ℝ) ^ (2 * k + 1)) *
              ∑ n ∈ s.preimage raise₃ hinj, ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ) := by
            simpa using
              (Finset.mul_sum (a := (2 : ℝ) ^ (2 * k + 1)) (s := s.preimage raise₃ hinj)
                (f := fun n => ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ))).symm
        _ ≤ ((2 : ℝ) ^ (2 * k + 1)) * ‖B‖ ^ (2 : ℕ) := by
            have hBsum :
                (∑ n ∈ s.preimage raise₃ hinj, ‖(B : ℕ → ℝ) n‖ ^ (2 : ℕ)) ≤ ‖B‖ ^ (2 : ℕ) := by
              simpa using
                (lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) hp B (s.preimage raise₃ hinj))
            have hnonneg : 0 ≤ (2 : ℝ) ^ (2 * k + 1) := by positivity
            exact mul_le_mul_of_nonneg_left hBsum hnonneg
        _ = (C0 * ‖B‖) ^ (2 : ℕ) := by
            have hC0sq : C0 ^ (2 : ℕ) = (2 : ℝ) ^ (2 * k + 1) := by
              simpa [C0] using (sqrt_two_mul_two_pow_sq (k := k))
            calc
              ((2 : ℝ) ^ (2 * k + 1)) * ‖B‖ ^ (2 : ℕ)
                  = (C0 ^ (2 : ℕ)) * ‖B‖ ^ (2 : ℕ) := by
                      simpa [hC0sq]
              _ = (C0 * ‖B‖) ^ (2 : ℕ) := by
                      simpa [mul_pow] using (mul_pow C0 ‖B‖ (2 : ℕ)).symm

    simpa using hsq

  simpa [coeffSeminormSeq_apply_eq_norm, A, B, C0] using hAB

/-! ## Coefficient seminorm shift: `lowerOpCLM` (coordinate 0) -/

lemma coeffSeminormSeq_lowerOpCLM0_le (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (lowerOpCLM ξ (0 : Fin STDimension) f) ≤
      (Real.sqrt 2) * coeffSeminormSeq ξ hξ (k + 1) f := by
  classical
  let A : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) k
      (normalizedCoeffRapidDecay ξ hξ (lowerOpCLM ξ (0 : Fin STDimension) f))
  let B : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) (k + 1) (normalizedCoeffRapidDecay ξ hξ f)
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  have hC : 0 ≤ (Real.sqrt 2) * ‖B‖ := by positivity
  have hAB : ‖A‖ ≤ (Real.sqrt 2) * ‖B‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := (Real.sqrt 2) * ‖B‖) hC ?_
    intro s
    have hsq :
        (∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ)) ≤ ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
      let g : ℕ → ℝ := fun n => ‖(A : ℕ → ℝ) n‖ ^ (2 : ℕ)

      have hpoint : ∀ n, g n ≤ (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₀ n)‖ ^ (2 : ℕ) := by
        intro n
        set c : ℝ := normalizedCoeffCLM_SpaceTime ξ hξ (raise₀ n) f

        have hAcoord :
            (A : ℕ → ℝ) n =
              (base₄ n) ^ k *
                Real.sqrt ((2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ)) * c := by
          have hcoord :
              (A : ℕ → ℝ) n =
                (base₄ n) ^ k *
                  normalizedCoeffCLM_SpaceTime ξ hξ n
                    (lowerOpCLM ξ (0 : Fin STDimension) f) := by
            simpa [A] using
              (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
                (f := lowerOpCLM ξ (0 : Fin STDimension) f) (n := n))
          rw [hcoord,
            normalizedCoeffCLM_SpaceTime_lowerOpCLM0 (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
          simp [c, mul_assoc]

        have ht0 : 0 ≤ (2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ) := by positivity
        have hg :
            g n =
              ((base₄ n) ^ k) ^ (2 : ℕ) *
                ((2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          dsimp [g]
          rw [hAcoord]
          exact
            norm_mul_sqrt_mul_sq (a := (base₄ n) ^ k)
              (t := (2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ)) (c := c) ht0

        have hpowA :
            ((base₄ n) ^ k) ^ (2 : ℕ) = (base₄ n) ^ (2 * k) := by
          calc
            ((base₄ n) ^ k) ^ (2 : ℕ) = (base₄ n) ^ (k * 2) := by
              simp [pow_mul]
            _ = (base₄ n) ^ (2 * k) := by
              simp [Nat.mul_comm]

        have hBcoord :
            (B : ℕ → ℝ) (raise₀ n) = (base₄ (raise₀ n)) ^ (k + 1) * c := by
          -- `c` is exactly the coefficient at the raised index.
          simpa [B, c] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k + 1) (f := f) (n := raise₀ n))

        have hBn :
            ‖(B : ℕ → ℝ) (raise₀ n)‖ ^ (2 : ℕ) =
              ((base₄ (raise₀ n)) ^ (k + 1)) ^ (2 : ℕ) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hBcoord, mul_assoc] using
            (norm_mul_sq (a := (base₄ (raise₀ n)) ^ (k + 1)) (c := c))

        have hpowB :
            ((base₄ (raise₀ n)) ^ (k + 1)) ^ (2 : ℕ) = (base₄ (raise₀ n)) ^ (2 * k + 2) := by
          calc
            ((base₄ (raise₀ n)) ^ (k + 1)) ^ (2 : ℕ) = (base₄ (raise₀ n)) ^ ((k + 1) * 2) := by
              simp [pow_mul]
            _ = (base₄ (raise₀ n)) ^ (2 * k + 2) := by
              have hk : (k + 1) * 2 = 2 * k + 2 := by
                calc
                  (k + 1) * 2 = k * 2 + 2 := by
                    simpa [Nat.succ_mul]
                  _ = 2 * k + 2 := by
                    simp [Nat.mul_comm]
              simpa [hk]

        have hBn2 :
            ‖(B : ℕ → ℝ) (raise₀ n)‖ ^ (2 : ℕ) =
              (base₄ (raise₀ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hpowB, mul_assoc] using hBn

        -- Scalar inequality: `base₄ n^(2k) * 2*(unpair+1) ≤ 2 * base₄(raise₀ n)^(2k+2)`.
        have hbase : base₄ n ≤ base₄ (raise₀ n) := base₄_le_base₄_raise₀ (n := n)
        have hbase0 : 0 ≤ base₄ n :=
          (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := n)).le
        have hbaser0 : 0 ≤ base₄ (raise₀ n) :=
          (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := raise₀ n)).le
        have hone : (1 : ℝ) ≤ base₄ (raise₀ n) :=
          OSforGFF.RapidDecaySeqMulti.one_le_base₄ (n := raise₀ n)
        have hpow_base : (base₄ n) ^ (2 * k) ≤ (base₄ (raise₀ n)) ^ (2 * k) :=
          pow_le_pow_left₀ hbase0 hbase _
        have hidx : ((unpair₄₁ n + 1 : ℕ) : ℝ) ≤ base₄ (raise₀ n) := by
          have : ((unpair₄₁ n + 1 : ℕ) : ℝ) ≤ base₄ n := by
            simpa [Nat.cast_add_one] using (unpair₄₁_add_one_le_base₄ (n := n))
          exact le_trans this (base₄_le_base₄_raise₀ (n := n))
        have hidx2 : (2 : ℝ) * ((unpair₄₁ n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * base₄ (raise₀ n) := by
          exact mul_le_mul_of_nonneg_left hidx (by norm_num)
        have hscalar :
            (base₄ n) ^ (2 * k) * (2 * ((unpair₄₁ n + 1 : ℕ) : ℝ)) ≤
              (2 : ℝ) * (base₄ (raise₀ n)) ^ (2 * k + 2) := by
          have hnonneg_pow : 0 ≤ (base₄ (raise₀ n)) ^ (2 * k) := pow_nonneg hbaser0 _
          calc
            (base₄ n) ^ (2 * k) * (2 * ((unpair₄₁ n + 1 : ℕ) : ℝ))
                ≤ (base₄ (raise₀ n)) ^ (2 * k) * (2 * ((unpair₄₁ n + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right hpow_base (by positivity)
            _ ≤ (base₄ (raise₀ n)) ^ (2 * k) * ((2 : ℝ) * base₄ (raise₀ n)) := by
                    exact mul_le_mul_of_nonneg_left hidx2 hnonneg_pow
            _ = (2 : ℝ) * (base₄ (raise₀ n)) ^ (2 * k + 1) := by
                    ring_nf
            _ ≤ (2 : ℝ) * (base₄ (raise₀ n)) ^ (2 * k + 2) := by
                    have : (base₄ (raise₀ n)) ^ (2 * k + 1) ≤ (base₄ (raise₀ n)) ^ (2 * k + 2) :=
                      pow_le_pow_right₀ hone (Nat.le_succ _)
                    exact mul_le_mul_of_nonneg_left this (by positivity)

        -- put everything together
        have hc2 : 0 ≤ ‖c‖ ^ (2 : ℕ) := by positivity
        have hmul := mul_le_mul_of_nonneg_right hscalar hc2
        -- rewrite `g n` and `‖B (raise₀ n)‖^2` and conclude
        rw [hg, hpowA]
        -- RHS of `hmul` is `2 * base^(2k+2) * ‖c‖^2`, rewrite with `hBn2`
        have hrhs :
            (2 : ℝ) * (base₄ (raise₀ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) =
              (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₀ n)‖ ^ (2 : ℕ) := by
          -- reassociate then use `hBn2`
          calc
            (2 : ℝ) * (base₄ (raise₀ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)
                = (2 : ℝ) * ((base₄ (raise₀ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)) := by
                    ring_nf
            _ = (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₀ n)‖ ^ (2 : ℕ) := by
                    rw [hBn2.symm]
        -- Now finish
        have hmul2 := hmul
        -- rewrite the RHS into `2 * ‖B (raise₀ n)‖^2`
        rw [hrhs] at hmul2
        exact hmul2

      calc
        ∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ) = ∑ i ∈ s, g i := by
          simp [g]
        _ ≤ ∑ i ∈ s, (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₀ i)‖ ^ (2 : ℕ) := by
            exact Finset.sum_le_sum fun i hi => hpoint i
        _ = (2 : ℝ) * ∑ i ∈ s, ‖(B : ℕ → ℝ) (raise₀ i)‖ ^ (2 : ℕ) := by
            simpa using
              (Finset.mul_sum (a := (2 : ℝ)) (s := s) (f := fun i => ‖(B : ℕ → ℝ) (raise₀ i)‖ ^ (2 : ℕ))).symm
        _ = (2 : ℝ) * ∑ m ∈ s.image raise₀, ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ) := by
            -- reindex the sum over the injective map `raise₀`
            have hinj : Set.InjOn raise₀ (↑s : Set ℕ) := Set.injOn_of_injective raise₀_injective
            -- `Finset.sum_image` gives the reverse equality; use its symmetry.
            simpa [mul_assoc] using congrArg (fun t => (2 : ℝ) * t)
              ((Finset.sum_image (f := fun m : ℕ => ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ)) (s := s)
                (g := raise₀) hinj).symm)
        _ ≤ (2 : ℝ) * ‖B‖ ^ (2 : ℕ) := by
            have hBsum :
                (∑ m ∈ s.image raise₀, ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ)) ≤ ‖B‖ ^ (2 : ℕ) := by
              simpa using
                (lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) hp B (s.image raise₀))
            have hnonneg : 0 ≤ (2 : ℝ) := by norm_num
            exact mul_le_mul_of_nonneg_left hBsum hnonneg
        _ = ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
            have hs : (Real.sqrt 2 : ℝ) ^ (2 : ℕ) = 2 := by
              simp [pow_two]
            calc
              (2 : ℝ) * ‖B‖ ^ (2 : ℕ)
                  = (Real.sqrt 2 : ℝ) ^ (2 : ℕ) * ‖B‖ ^ (2 : ℕ) := by
                      simpa [hs]
              _ = ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
                      simpa [mul_pow] using (mul_pow (Real.sqrt 2) ‖B‖ (2 : ℕ)).symm

    simpa using hsq

  simpa [coeffSeminormSeq_apply_eq_norm, A, B] using hAB

/-! ## Coefficient seminorm shift: `lowerOpCLM` (coordinate 1) -/

lemma coeffSeminormSeq_lowerOpCLM1_le (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (lowerOpCLM ξ (1 : Fin STDimension) f) ≤
      (Real.sqrt 2) * coeffSeminormSeq ξ hξ (k + 1) f := by
  classical
  let A : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) k
      (normalizedCoeffRapidDecay ξ hξ (lowerOpCLM ξ (1 : Fin STDimension) f))
  let B : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) (k + 1) (normalizedCoeffRapidDecay ξ hξ f)
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  have hC : 0 ≤ (Real.sqrt 2) * ‖B‖ := by positivity
  have hAB : ‖A‖ ≤ (Real.sqrt 2) * ‖B‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := (Real.sqrt 2) * ‖B‖) hC ?_
    intro s
    have hsq :
        (∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ)) ≤ ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
      let g : ℕ → ℝ := fun n => ‖(A : ℕ → ℝ) n‖ ^ (2 : ℕ)

      have hpoint : ∀ n, g n ≤ (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₁ n)‖ ^ (2 : ℕ) := by
        intro n
        set c : ℝ := normalizedCoeffCLM_SpaceTime ξ hξ (raise₁ n) f

        have hAcoord :
            (A : ℕ → ℝ) n =
              (base₄ n) ^ k *
                Real.sqrt ((2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ)) * c := by
          have hcoord :
              (A : ℕ → ℝ) n =
                (base₄ n) ^ k *
                  normalizedCoeffCLM_SpaceTime ξ hξ n
                    (lowerOpCLM ξ (1 : Fin STDimension) f) := by
            simpa [A] using
              (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
                (f := lowerOpCLM ξ (1 : Fin STDimension) f) (n := n))
          rw [hcoord,
            normalizedCoeffCLM_SpaceTime_lowerOpCLM1 (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
          simp [c, mul_assoc]

        have ht0 : 0 ≤ (2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ) := by positivity
        have hg :
            g n =
              ((base₄ n) ^ k) ^ (2 : ℕ) *
                ((2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          dsimp [g]
          rw [hAcoord]
          exact
            norm_mul_sqrt_mul_sq (a := (base₄ n) ^ k)
              (t := (2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ)) (c := c) ht0

        have hpowA :
            ((base₄ n) ^ k) ^ (2 : ℕ) = (base₄ n) ^ (2 * k) := by
          calc
            ((base₄ n) ^ k) ^ (2 : ℕ) = (base₄ n) ^ (k * 2) := by
              simp [pow_mul]
            _ = (base₄ n) ^ (2 * k) := by
              simp [Nat.mul_comm]

        have hBcoord :
            (B : ℕ → ℝ) (raise₁ n) = (base₄ (raise₁ n)) ^ (k + 1) * c := by
          simpa [B, c] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k + 1) (f := f) (n := raise₁ n))

        have hBn :
            ‖(B : ℕ → ℝ) (raise₁ n)‖ ^ (2 : ℕ) =
              ((base₄ (raise₁ n)) ^ (k + 1)) ^ (2 : ℕ) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hBcoord, mul_assoc] using
            (norm_mul_sq (a := (base₄ (raise₁ n)) ^ (k + 1)) (c := c))

        have hpowB :
            ((base₄ (raise₁ n)) ^ (k + 1)) ^ (2 : ℕ) = (base₄ (raise₁ n)) ^ (2 * k + 2) := by
          calc
            ((base₄ (raise₁ n)) ^ (k + 1)) ^ (2 : ℕ) = (base₄ (raise₁ n)) ^ ((k + 1) * 2) := by
              simp [pow_mul]
            _ = (base₄ (raise₁ n)) ^ (2 * k + 2) := by
              have hk : (k + 1) * 2 = 2 * k + 2 := by
                calc
                  (k + 1) * 2 = k * 2 + 2 := by
                    simpa [Nat.succ_mul]
                  _ = 2 * k + 2 := by
                    simp [Nat.mul_comm]
              simpa [hk]

        have hBn2 :
            ‖(B : ℕ → ℝ) (raise₁ n)‖ ^ (2 : ℕ) =
              (base₄ (raise₁ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hpowB, mul_assoc] using hBn

        -- scalar inequality
        have hbase : base₄ n ≤ base₄ (raise₁ n) := base₄_le_base₄_raise₁ (n := n)
        have hbase0 : 0 ≤ base₄ n := (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := n)).le
        have hbaser : 0 ≤ base₄ (raise₁ n) := (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := raise₁ n)).le
        have hone : (1 : ℝ) ≤ base₄ (raise₁ n) := OSforGFF.RapidDecaySeqMulti.one_le_base₄ (n := raise₁ n)
        have hpow_base : (base₄ n) ^ (2 * k) ≤ (base₄ (raise₁ n)) ^ (2 * k) :=
          pow_le_pow_left₀ hbase0 hbase _
        have hidx : ((unpair₄₂ n + 1 : ℕ) : ℝ) ≤ base₄ (raise₁ n) := by
          have : ((unpair₄₂ n + 1 : ℕ) : ℝ) ≤ base₄ n := by
            simpa [Nat.cast_add_one] using (unpair₄₂_add_one_le_base₄ (n := n))
          exact le_trans this (base₄_le_base₄_raise₁ (n := n))
        have hidx2 : (2 : ℝ) * ((unpair₄₂ n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * base₄ (raise₁ n) := by
          exact mul_le_mul_of_nonneg_left hidx (by norm_num)
        have hscalar :
            (base₄ n) ^ (2 * k) * (2 * ((unpair₄₂ n + 1 : ℕ) : ℝ)) ≤
              (2 : ℝ) * (base₄ (raise₁ n)) ^ (2 * k + 2) := by
          have hnonneg_pow : 0 ≤ (base₄ (raise₁ n)) ^ (2 * k) := pow_nonneg hbaser _
          calc
            (base₄ n) ^ (2 * k) * (2 * ((unpair₄₂ n + 1 : ℕ) : ℝ))
                ≤ (base₄ (raise₁ n)) ^ (2 * k) * (2 * ((unpair₄₂ n + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right hpow_base (by positivity)
            _ ≤ (base₄ (raise₁ n)) ^ (2 * k) * ((2 : ℝ) * base₄ (raise₁ n)) := by
                    exact mul_le_mul_of_nonneg_left hidx2 hnonneg_pow
            _ = (2 : ℝ) * (base₄ (raise₁ n)) ^ (2 * k + 1) := by
                    ring_nf
            _ ≤ (2 : ℝ) * (base₄ (raise₁ n)) ^ (2 * k + 2) := by
                    have : (base₄ (raise₁ n)) ^ (2 * k + 1) ≤ (base₄ (raise₁ n)) ^ (2 * k + 2) :=
                      pow_le_pow_right₀ hone (Nat.le_succ _)
                    exact mul_le_mul_of_nonneg_left this (by positivity)

        have hc2 : 0 ≤ ‖c‖ ^ (2 : ℕ) := by positivity
        have hmul := mul_le_mul_of_nonneg_right hscalar hc2
        rw [hg, hpowA]
        have hrhs :
            (2 : ℝ) * (base₄ (raise₁ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) =
              (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₁ n)‖ ^ (2 : ℕ) := by
          calc
            (2 : ℝ) * (base₄ (raise₁ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)
                = (2 : ℝ) * ((base₄ (raise₁ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)) := by
                    ring_nf
            _ = (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₁ n)‖ ^ (2 : ℕ) := by
                    rw [hBn2.symm]
        have hmul2 := hmul
        rw [hrhs] at hmul2
        exact hmul2

      calc
        ∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ) = ∑ i ∈ s, g i := by
          simp [g]
        _ ≤ ∑ i ∈ s, (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₁ i)‖ ^ (2 : ℕ) := by
            exact Finset.sum_le_sum fun i hi => hpoint i
        _ = (2 : ℝ) * ∑ i ∈ s, ‖(B : ℕ → ℝ) (raise₁ i)‖ ^ (2 : ℕ) := by
            simpa using
              (Finset.mul_sum (a := (2 : ℝ)) (s := s)
                (f := fun i => ‖(B : ℕ → ℝ) (raise₁ i)‖ ^ (2 : ℕ))).symm
        _ = (2 : ℝ) * ∑ m ∈ s.image raise₁, ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ) := by
            have hinj : Set.InjOn raise₁ (↑s : Set ℕ) := Set.injOn_of_injective raise₁_injective
            simpa [mul_assoc] using congrArg (fun t => (2 : ℝ) * t)
              ((Finset.sum_image (f := fun m : ℕ => ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ)) (s := s)
                (g := raise₁) hinj).symm)
        _ ≤ (2 : ℝ) * ‖B‖ ^ (2 : ℕ) := by
            have hBsum :
                (∑ m ∈ s.image raise₁, ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ)) ≤ ‖B‖ ^ (2 : ℕ) := by
              simpa using
                (lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) hp B (s.image raise₁))
            have hnonneg : 0 ≤ (2 : ℝ) := by norm_num
            exact mul_le_mul_of_nonneg_left hBsum hnonneg
        _ = ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
            have hs : (Real.sqrt 2 : ℝ) ^ (2 : ℕ) = 2 := by
              simp [pow_two]
            calc
              (2 : ℝ) * ‖B‖ ^ (2 : ℕ)
                  = (Real.sqrt 2 : ℝ) ^ (2 : ℕ) * ‖B‖ ^ (2 : ℕ) := by
                      simpa [hs]
              _ = ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
                      simpa [mul_pow] using (mul_pow (Real.sqrt 2) ‖B‖ (2 : ℕ)).symm

    simpa using hsq

  simpa [coeffSeminormSeq_apply_eq_norm, A, B] using hAB

/-! ## Coefficient seminorm shift: `lowerOpCLM` (coordinate 2) -/

lemma coeffSeminormSeq_lowerOpCLM2_le (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (lowerOpCLM ξ (2 : Fin STDimension) f) ≤
      (Real.sqrt 2) * coeffSeminormSeq ξ hξ (k + 1) f := by
  classical
  let A : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) k
      (normalizedCoeffRapidDecay ξ hξ (lowerOpCLM ξ (2 : Fin STDimension) f))
  let B : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) (k + 1) (normalizedCoeffRapidDecay ξ hξ f)
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  have hC : 0 ≤ (Real.sqrt 2) * ‖B‖ := by positivity
  have hAB : ‖A‖ ≤ (Real.sqrt 2) * ‖B‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := (Real.sqrt 2) * ‖B‖) hC ?_
    intro s
    have hsq :
        (∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ)) ≤ ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
      let g : ℕ → ℝ := fun n => ‖(A : ℕ → ℝ) n‖ ^ (2 : ℕ)

      have hpoint : ∀ n, g n ≤ (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₂ n)‖ ^ (2 : ℕ) := by
        intro n
        set c : ℝ := normalizedCoeffCLM_SpaceTime ξ hξ (raise₂ n) f

        have hAcoord :
            (A : ℕ → ℝ) n =
              (base₄ n) ^ k *
                Real.sqrt ((2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ)) * c := by
          have hcoord :
              (A : ℕ → ℝ) n =
                (base₄ n) ^ k *
                  normalizedCoeffCLM_SpaceTime ξ hξ n
                    (lowerOpCLM ξ (2 : Fin STDimension) f) := by
            simpa [A] using
              (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
                (f := lowerOpCLM ξ (2 : Fin STDimension) f) (n := n))
          rw [hcoord,
            normalizedCoeffCLM_SpaceTime_lowerOpCLM2 (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
          simp [c, mul_assoc]

        have ht0 : 0 ≤ (2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ) := by positivity
        have hg :
            g n =
              ((base₄ n) ^ k) ^ (2 : ℕ) *
                ((2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          dsimp [g]
          rw [hAcoord]
          exact
            norm_mul_sqrt_mul_sq (a := (base₄ n) ^ k)
              (t := (2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ)) (c := c) ht0

        have hpowA :
            ((base₄ n) ^ k) ^ (2 : ℕ) = (base₄ n) ^ (2 * k) := by
          calc
            ((base₄ n) ^ k) ^ (2 : ℕ) = (base₄ n) ^ (k * 2) := by
              simp [pow_mul]
            _ = (base₄ n) ^ (2 * k) := by
              simp [Nat.mul_comm]

        have hBcoord :
            (B : ℕ → ℝ) (raise₂ n) = (base₄ (raise₂ n)) ^ (k + 1) * c := by
          simpa [B, c] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k + 1) (f := f) (n := raise₂ n))

        have hBn :
            ‖(B : ℕ → ℝ) (raise₂ n)‖ ^ (2 : ℕ) =
              ((base₄ (raise₂ n)) ^ (k + 1)) ^ (2 : ℕ) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hBcoord, mul_assoc] using
            (norm_mul_sq (a := (base₄ (raise₂ n)) ^ (k + 1)) (c := c))

        have hpowB :
            ((base₄ (raise₂ n)) ^ (k + 1)) ^ (2 : ℕ) = (base₄ (raise₂ n)) ^ (2 * k + 2) := by
          calc
            ((base₄ (raise₂ n)) ^ (k + 1)) ^ (2 : ℕ) = (base₄ (raise₂ n)) ^ ((k + 1) * 2) := by
              simp [pow_mul]
            _ = (base₄ (raise₂ n)) ^ (2 * k + 2) := by
              have hk : (k + 1) * 2 = 2 * k + 2 := by
                calc
                  (k + 1) * 2 = k * 2 + 2 := by
                    simpa [Nat.succ_mul]
                  _ = 2 * k + 2 := by
                    simp [Nat.mul_comm]
              simpa [hk]

        have hBn2 :
            ‖(B : ℕ → ℝ) (raise₂ n)‖ ^ (2 : ℕ) =
              (base₄ (raise₂ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hpowB, mul_assoc] using hBn

        -- scalar inequality
        have hbase : base₄ n ≤ base₄ (raise₂ n) := base₄_le_base₄_raise₂ (n := n)
        have hbase0 : 0 ≤ base₄ n := (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := n)).le
        have hbaser : 0 ≤ base₄ (raise₂ n) := (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := raise₂ n)).le
        have hone : (1 : ℝ) ≤ base₄ (raise₂ n) := OSforGFF.RapidDecaySeqMulti.one_le_base₄ (n := raise₂ n)
        have hpow_base : (base₄ n) ^ (2 * k) ≤ (base₄ (raise₂ n)) ^ (2 * k) :=
          pow_le_pow_left₀ hbase0 hbase _
        have hidx : ((unpair₄₃ n + 1 : ℕ) : ℝ) ≤ base₄ (raise₂ n) := by
          have : ((unpair₄₃ n + 1 : ℕ) : ℝ) ≤ base₄ n := by
            simpa [Nat.cast_add_one] using (unpair₄₃_add_one_le_base₄ (n := n))
          exact le_trans this (base₄_le_base₄_raise₂ (n := n))
        have hidx2 : (2 : ℝ) * ((unpair₄₃ n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * base₄ (raise₂ n) := by
          exact mul_le_mul_of_nonneg_left hidx (by norm_num)
        have hscalar :
            (base₄ n) ^ (2 * k) * (2 * ((unpair₄₃ n + 1 : ℕ) : ℝ)) ≤
              (2 : ℝ) * (base₄ (raise₂ n)) ^ (2 * k + 2) := by
          have hnonneg_pow : 0 ≤ (base₄ (raise₂ n)) ^ (2 * k) := pow_nonneg hbaser _
          calc
            (base₄ n) ^ (2 * k) * (2 * ((unpair₄₃ n + 1 : ℕ) : ℝ))
                ≤ (base₄ (raise₂ n)) ^ (2 * k) * (2 * ((unpair₄₃ n + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right hpow_base (by positivity)
            _ ≤ (base₄ (raise₂ n)) ^ (2 * k) * ((2 : ℝ) * base₄ (raise₂ n)) := by
                    exact mul_le_mul_of_nonneg_left hidx2 hnonneg_pow
            _ = (2 : ℝ) * (base₄ (raise₂ n)) ^ (2 * k + 1) := by
                    ring_nf
            _ ≤ (2 : ℝ) * (base₄ (raise₂ n)) ^ (2 * k + 2) := by
                    have : (base₄ (raise₂ n)) ^ (2 * k + 1) ≤ (base₄ (raise₂ n)) ^ (2 * k + 2) :=
                      pow_le_pow_right₀ hone (Nat.le_succ _)
                    exact mul_le_mul_of_nonneg_left this (by positivity)

        have hc2 : 0 ≤ ‖c‖ ^ (2 : ℕ) := by positivity
        have hmul := mul_le_mul_of_nonneg_right hscalar hc2
        rw [hg, hpowA]
        have hrhs :
            (2 : ℝ) * (base₄ (raise₂ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) =
              (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₂ n)‖ ^ (2 : ℕ) := by
          calc
            (2 : ℝ) * (base₄ (raise₂ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)
                = (2 : ℝ) * ((base₄ (raise₂ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)) := by
                    ring_nf
            _ = (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₂ n)‖ ^ (2 : ℕ) := by
                    rw [hBn2.symm]
        have hmul2 := hmul
        rw [hrhs] at hmul2
        exact hmul2

      calc
        ∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ) = ∑ i ∈ s, g i := by
          simp [g]
        _ ≤ ∑ i ∈ s, (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₂ i)‖ ^ (2 : ℕ) := by
            exact Finset.sum_le_sum fun i hi => hpoint i
        _ = (2 : ℝ) * ∑ i ∈ s, ‖(B : ℕ → ℝ) (raise₂ i)‖ ^ (2 : ℕ) := by
            simpa using
              (Finset.mul_sum (a := (2 : ℝ)) (s := s)
                (f := fun i => ‖(B : ℕ → ℝ) (raise₂ i)‖ ^ (2 : ℕ))).symm
        _ = (2 : ℝ) * ∑ m ∈ s.image raise₂, ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ) := by
            have hinj : Set.InjOn raise₂ (↑s : Set ℕ) := Set.injOn_of_injective raise₂_injective
            simpa [mul_assoc] using congrArg (fun t => (2 : ℝ) * t)
              ((Finset.sum_image (f := fun m : ℕ => ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ)) (s := s)
                (g := raise₂) hinj).symm)
        _ ≤ (2 : ℝ) * ‖B‖ ^ (2 : ℕ) := by
            have hBsum :
                (∑ m ∈ s.image raise₂, ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ)) ≤ ‖B‖ ^ (2 : ℕ) := by
              simpa using
                (lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) hp B (s.image raise₂))
            have hnonneg : 0 ≤ (2 : ℝ) := by norm_num
            exact mul_le_mul_of_nonneg_left hBsum hnonneg
        _ = ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
            have hs : (Real.sqrt 2 : ℝ) ^ (2 : ℕ) = 2 := by
              simp [pow_two]
            calc
              (2 : ℝ) * ‖B‖ ^ (2 : ℕ)
                  = (Real.sqrt 2 : ℝ) ^ (2 : ℕ) * ‖B‖ ^ (2 : ℕ) := by
                      simpa [hs]
              _ = ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
                      simpa [mul_pow] using (mul_pow (Real.sqrt 2) ‖B‖ (2 : ℕ)).symm

    simpa using hsq

  simpa [coeffSeminormSeq_apply_eq_norm, A, B] using hAB

/-! ## Coefficient seminorm shift: `lowerOpCLM` (coordinate 3) -/

lemma coeffSeminormSeq_lowerOpCLM3_le (ξ : ℝ) (hξ : ξ ≠ 0) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (lowerOpCLM ξ (3 : Fin STDimension) f) ≤
      (Real.sqrt 2) * coeffSeminormSeq ξ hξ (k + 1) f := by
  classical
  let A : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) k
      (normalizedCoeffRapidDecay ξ hξ (lowerOpCLM ξ (3 : Fin STDimension) f))
  let B : H :=
    OSforGFF.RapidDecaySeqBase.Space.toL2ₗ (base := base₄) (k + 1) (normalizedCoeffRapidDecay ξ hξ f)
  have hp : (0 : ℝ) < ((2 : ℝ≥0∞).toReal) := by norm_num
  have hC : 0 ≤ (Real.sqrt 2) * ‖B‖ := by positivity
  have hAB : ‖A‖ ≤ (Real.sqrt 2) * ‖B‖ := by
    refine lp.norm_le_of_forall_sum_le (p := (2 : ℝ≥0∞)) hp (C := (Real.sqrt 2) * ‖B‖) hC ?_
    intro s
    have hsq :
        (∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ)) ≤ ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
      let g : ℕ → ℝ := fun n => ‖(A : ℕ → ℝ) n‖ ^ (2 : ℕ)

      have hpoint : ∀ n, g n ≤ (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₃ n)‖ ^ (2 : ℕ) := by
        intro n
        set c : ℝ := normalizedCoeffCLM_SpaceTime ξ hξ (raise₃ n) f

        have hAcoord :
            (A : ℕ → ℝ) n =
              (base₄ n) ^ k *
                Real.sqrt ((2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ)) * c := by
          have hcoord :
              (A : ℕ → ℝ) n =
                (base₄ n) ^ k *
                  normalizedCoeffCLM_SpaceTime ξ hξ n
                    (lowerOpCLM ξ (3 : Fin STDimension) f) := by
            simpa [A] using
              (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k)
                (f := lowerOpCLM ξ (3 : Fin STDimension) f) (n := n))
          rw [hcoord,
            normalizedCoeffCLM_SpaceTime_lowerOpCLM3 (ξ := ξ) (hξ := hξ) (n := n) (f := f)]
          simp [c, mul_assoc]

        have ht0 : 0 ≤ (2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ) := by positivity
        have hg :
            g n =
              ((base₄ n) ^ k) ^ (2 : ℕ) *
                ((2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ)) * ‖c‖ ^ (2 : ℕ) := by
          dsimp [g]
          rw [hAcoord]
          exact
            norm_mul_sqrt_mul_sq (a := (base₄ n) ^ k)
              (t := (2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ)) (c := c) ht0

        have hpowA :
            ((base₄ n) ^ k) ^ (2 : ℕ) = (base₄ n) ^ (2 * k) := by
          calc
            ((base₄ n) ^ k) ^ (2 : ℕ) = (base₄ n) ^ (k * 2) := by
              simp [pow_mul]
            _ = (base₄ n) ^ (2 * k) := by
              simp [Nat.mul_comm]

        have hBcoord :
            (B : ℕ → ℝ) (raise₃ n) = (base₄ (raise₃ n)) ^ (k + 1) * c := by
          simpa [B, c] using
            (coeffSeminormSeq_toL2_apply (ξ := ξ) (hξ := hξ) (k := k + 1) (f := f) (n := raise₃ n))

        have hBn :
            ‖(B : ℕ → ℝ) (raise₃ n)‖ ^ (2 : ℕ) =
              ((base₄ (raise₃ n)) ^ (k + 1)) ^ (2 : ℕ) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hBcoord, mul_assoc] using
            (norm_mul_sq (a := (base₄ (raise₃ n)) ^ (k + 1)) (c := c))

        have hpowB :
            ((base₄ (raise₃ n)) ^ (k + 1)) ^ (2 : ℕ) = (base₄ (raise₃ n)) ^ (2 * k + 2) := by
          calc
            ((base₄ (raise₃ n)) ^ (k + 1)) ^ (2 : ℕ) = (base₄ (raise₃ n)) ^ ((k + 1) * 2) := by
              simp [pow_mul]
            _ = (base₄ (raise₃ n)) ^ (2 * k + 2) := by
              have hk : (k + 1) * 2 = 2 * k + 2 := by
                calc
                  (k + 1) * 2 = k * 2 + 2 := by
                    simpa [Nat.succ_mul]
                  _ = 2 * k + 2 := by
                    simp [Nat.mul_comm]
              simpa [hk]

        have hBn2 :
            ‖(B : ℕ → ℝ) (raise₃ n)‖ ^ (2 : ℕ) =
              (base₄ (raise₃ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) := by
          simpa [hpowB, mul_assoc] using hBn

        -- scalar inequality
        have hbase : base₄ n ≤ base₄ (raise₃ n) := base₄_le_base₄_raise₃ (n := n)
        have hbase0 : 0 ≤ base₄ n := (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := n)).le
        have hbaser : 0 ≤ base₄ (raise₃ n) := (OSforGFF.RapidDecaySeqMulti.base₄_pos (n := raise₃ n)).le
        have hone : (1 : ℝ) ≤ base₄ (raise₃ n) := OSforGFF.RapidDecaySeqMulti.one_le_base₄ (n := raise₃ n)
        have hpow_base : (base₄ n) ^ (2 * k) ≤ (base₄ (raise₃ n)) ^ (2 * k) :=
          pow_le_pow_left₀ hbase0 hbase _
        have hidx : ((unpair₄₄ n + 1 : ℕ) : ℝ) ≤ base₄ (raise₃ n) := by
          have : ((unpair₄₄ n + 1 : ℕ) : ℝ) ≤ base₄ n := by
            simpa [Nat.cast_add_one] using (unpair₄₄_add_one_le_base₄ (n := n))
          exact le_trans this (base₄_le_base₄_raise₃ (n := n))
        have hidx2 : (2 : ℝ) * ((unpair₄₄ n + 1 : ℕ) : ℝ) ≤ (2 : ℝ) * base₄ (raise₃ n) := by
          exact mul_le_mul_of_nonneg_left hidx (by norm_num)
        have hscalar :
            (base₄ n) ^ (2 * k) * (2 * ((unpair₄₄ n + 1 : ℕ) : ℝ)) ≤
              (2 : ℝ) * (base₄ (raise₃ n)) ^ (2 * k + 2) := by
          have hnonneg_pow : 0 ≤ (base₄ (raise₃ n)) ^ (2 * k) := pow_nonneg hbaser _
          calc
            (base₄ n) ^ (2 * k) * (2 * ((unpair₄₄ n + 1 : ℕ) : ℝ))
                ≤ (base₄ (raise₃ n)) ^ (2 * k) * (2 * ((unpair₄₄ n + 1 : ℕ) : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right hpow_base (by positivity)
            _ ≤ (base₄ (raise₃ n)) ^ (2 * k) * ((2 : ℝ) * base₄ (raise₃ n)) := by
                    exact mul_le_mul_of_nonneg_left hidx2 hnonneg_pow
            _ = (2 : ℝ) * (base₄ (raise₃ n)) ^ (2 * k + 1) := by
                    ring_nf
            _ ≤ (2 : ℝ) * (base₄ (raise₃ n)) ^ (2 * k + 2) := by
                    have : (base₄ (raise₃ n)) ^ (2 * k + 1) ≤ (base₄ (raise₃ n)) ^ (2 * k + 2) :=
                      pow_le_pow_right₀ hone (Nat.le_succ _)
                    exact mul_le_mul_of_nonneg_left this (by positivity)

        have hc2 : 0 ≤ ‖c‖ ^ (2 : ℕ) := by positivity
        have hmul := mul_le_mul_of_nonneg_right hscalar hc2
        rw [hg, hpowA]
        have hrhs :
            (2 : ℝ) * (base₄ (raise₃ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ) =
              (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₃ n)‖ ^ (2 : ℕ) := by
          calc
            (2 : ℝ) * (base₄ (raise₃ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)
                = (2 : ℝ) * ((base₄ (raise₃ n)) ^ (2 * k + 2) * ‖c‖ ^ (2 : ℕ)) := by
                    ring_nf
            _ = (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₃ n)‖ ^ (2 : ℕ) := by
                    rw [hBn2.symm]
        have hmul2 := hmul
        rw [hrhs] at hmul2
        exact hmul2

      calc
        ∑ i ∈ s, ‖(A : ℕ → ℝ) i‖ ^ (2 : ℕ) = ∑ i ∈ s, g i := by
          simp [g]
        _ ≤ ∑ i ∈ s, (2 : ℝ) * ‖(B : ℕ → ℝ) (raise₃ i)‖ ^ (2 : ℕ) := by
            exact Finset.sum_le_sum fun i hi => hpoint i
        _ = (2 : ℝ) * ∑ i ∈ s, ‖(B : ℕ → ℝ) (raise₃ i)‖ ^ (2 : ℕ) := by
            simpa using
              (Finset.mul_sum (a := (2 : ℝ)) (s := s)
                (f := fun i => ‖(B : ℕ → ℝ) (raise₃ i)‖ ^ (2 : ℕ))).symm
        _ = (2 : ℝ) * ∑ m ∈ s.image raise₃, ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ) := by
            have hinj : Set.InjOn raise₃ (↑s : Set ℕ) := Set.injOn_of_injective raise₃_injective
            simpa [mul_assoc] using congrArg (fun t => (2 : ℝ) * t)
              ((Finset.sum_image (f := fun m : ℕ => ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ)) (s := s)
                (g := raise₃) hinj).symm)
        _ ≤ (2 : ℝ) * ‖B‖ ^ (2 : ℕ) := by
            have hBsum :
                (∑ m ∈ s.image raise₃, ‖(B : ℕ → ℝ) m‖ ^ (2 : ℕ)) ≤ ‖B‖ ^ (2 : ℕ) := by
              simpa using
                (lp.sum_rpow_le_norm_rpow (p := (2 : ℝ≥0∞)) hp B (s.image raise₃))
            have hnonneg : 0 ≤ (2 : ℝ) := by norm_num
            exact mul_le_mul_of_nonneg_left hBsum hnonneg
        _ = ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
            have hs : (Real.sqrt 2 : ℝ) ^ (2 : ℕ) = 2 := by
              simp [pow_two]
            calc
              (2 : ℝ) * ‖B‖ ^ (2 : ℕ)
                  = (Real.sqrt 2 : ℝ) ^ (2 : ℕ) * ‖B‖ ^ (2 : ℕ) := by
                      simpa [hs]
              _ = ((Real.sqrt 2) * ‖B‖) ^ (2 : ℕ) := by
                      simpa [mul_pow] using (mul_pow (Real.sqrt 2) ‖B‖ (2 : ℕ)).symm

    simpa using hsq

  simpa [coeffSeminormSeq_apply_eq_norm, A, B] using hAB

/-! ## Bounds for `mulCoordCLM` and `derivCoordCLM` in coefficient seminorms -/

lemma coeffSeminormSeq_raiseOpCLM_le (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f) ≤
      (Real.sqrt 2 * (2 : ℝ) ^ k) * coeffSeminormSeq ξ hξ (k + 1) f := by
  fin_cases i
  · simpa using (coeffSeminormSeq_raiseOpCLM0_le (ξ := ξ) (hξ := hξ) (k := k) (f := f))
  · simpa using (coeffSeminormSeq_raiseOpCLM1_le (ξ := ξ) (hξ := hξ) (k := k) (f := f))
  · simpa using (coeffSeminormSeq_raiseOpCLM2_le (ξ := ξ) (hξ := hξ) (k := k) (f := f))
  · simpa using (coeffSeminormSeq_raiseOpCLM3_le (ξ := ξ) (hξ := hξ) (k := k) (f := f))

lemma coeffSeminormSeq_lowerOpCLM_le (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f) ≤
      (Real.sqrt 2) * coeffSeminormSeq ξ hξ (k + 1) f := by
  fin_cases i
  · simpa using (coeffSeminormSeq_lowerOpCLM0_le (ξ := ξ) (hξ := hξ) (k := k) (f := f))
  · simpa using (coeffSeminormSeq_lowerOpCLM1_le (ξ := ξ) (hξ := hξ) (k := k) (f := f))
  · simpa using (coeffSeminormSeq_lowerOpCLM2_le (ξ := ξ) (hξ := hξ) (k := k) (f := f))
  · simpa using (coeffSeminormSeq_lowerOpCLM3_le (ξ := ξ) (hξ := hξ) (k := k) (f := f))

lemma coeffSeminormSeq_mulCoordCLM_le (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (mulCoordCLM i f) ≤
      (‖(ξ / 2 : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k + 1)) * coeffSeminormSeq ξ hξ (k + 1) f := by
  -- express `mulCoordCLM` via `raiseOpCLM` and `lowerOpCLM`
  have hmul :
      mulCoordCLM i f = (ξ / 2) • (raiseOpCLM ξ i f + lowerOpCLM ξ i f) := by
    -- `raise + lower = (2 * ξ⁻¹) • mul`
    have hsum :
        raiseOpCLM ξ i f + lowerOpCLM ξ i f = (2 * ξ⁻¹) • mulCoordCLM i f := by
      -- expand and cancel the derivative terms
      calc
        raiseOpCLM ξ i f + lowerOpCLM ξ i f
            = ((ξ⁻¹) • mulCoordCLM i f - ξ • derivCoordCLM i f)
                + ((ξ⁻¹) • mulCoordCLM i f + ξ • derivCoordCLM i f) := by
                  simp [raiseOpCLM_apply, lowerOpCLM_apply]
        _ = ((ξ⁻¹) • mulCoordCLM i f - ξ • derivCoordCLM i f)
                + (ξ • derivCoordCLM i f + (ξ⁻¹) • mulCoordCLM i f) := by
                  simp [add_comm, add_left_comm, add_assoc]
        _ = ((ξ⁻¹) • mulCoordCLM i f) + (ξ⁻¹) • mulCoordCLM i f := by
                  simpa [sub_eq_add_neg, add_assoc] using
                    (sub_add_add_cancel ((ξ⁻¹) • mulCoordCLM i f) (ξ • derivCoordCLM i f)
                      ((ξ⁻¹) • mulCoordCLM i f))
        _ = (2 : ℝ) • ((ξ⁻¹) • mulCoordCLM i f) := by
                  simpa [two_smul]
        _ = (2 * ξ⁻¹) • mulCoordCLM i f := by
                  simp [smul_smul, mul_assoc]
    -- now cancel the scalar factor
    have hscalar : (ξ / 2 : ℝ) * (2 * ξ⁻¹) = 1 := by
      calc
        (ξ / 2 : ℝ) * (2 * ξ⁻¹) = ((ξ / 2 : ℝ) * 2) * ξ⁻¹ := by
          ring_nf
        _ = ξ * ξ⁻¹ := by
          simp [div_eq_mul_inv, mul_assoc]
        _ = 1 := by
          simpa [hξ] using (mul_inv_cancel hξ)
    have hcancel :
        (ξ / 2) • (raiseOpCLM ξ i f + lowerOpCLM ξ i f) = mulCoordCLM i f := by
      have hsmul := congrArg (fun x : TestFunction => (ξ / 2) • x) hsum
      -- simplify the RHS scalar product to `mulCoordCLM i f`
      have hright :
          (ξ / 2) • ((2 * ξ⁻¹) • mulCoordCLM i f) = mulCoordCLM i f := by
        calc
          (ξ / 2) • ((2 * ξ⁻¹) • mulCoordCLM i f)
              = ((ξ / 2 : ℝ) * (2 * ξ⁻¹)) • mulCoordCLM i f := by
                  simp [smul_smul, mul_assoc]
          _ = (1 : ℝ) • mulCoordCLM i f := by
                  simp [hscalar]
          _ = mulCoordCLM i f := by simp
      exact hsmul.trans hright
    exact hcancel.symm

  -- apply seminorm estimates
  -- start by rewriting with `hmul`
  have hsmul :
      coeffSeminormSeq ξ hξ k (mulCoordCLM i f) =
        ‖(ξ / 2 : ℝ)‖ * coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f + lowerOpCLM ξ i f) := by
    -- `p (a • x) = ‖a‖ * p x`, then rewrite the argument using `hmul`
    have h :=
      (map_smul_eq_mul (coeffSeminormSeq ξ hξ k) (ξ / 2) (raiseOpCLM ξ i f + lowerOpCLM ξ i f))
    -- avoid `simp` recursion: rewrite by `rw` only
    calc
      coeffSeminormSeq ξ hξ k (mulCoordCLM i f)
          = coeffSeminormSeq ξ hξ k ((ξ / 2) • (raiseOpCLM ξ i f + lowerOpCLM ξ i f)) := by
              rw [hmul]
        _ = ‖(ξ / 2 : ℝ)‖ * coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f + lowerOpCLM ξ i f) := by
              simpa using h
  -- triangle inequality on the sum
  have hadd :
      coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f + lowerOpCLM ξ i f) ≤
        coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f) +
          coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f) :=
    map_add_le_add (coeffSeminormSeq ξ hξ k) _ _
  -- use raise/lower shift bounds
  have hra :
      coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f) ≤
        (Real.sqrt 2 * (2 : ℝ) ^ k) * coeffSeminormSeq ξ hξ (k + 1) f :=
    coeffSeminormSeq_raiseOpCLM_le (ξ := ξ) (hξ := hξ) (i := i) (k := k) (f := f)
  have hlo :
      coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f) ≤
        (Real.sqrt 2) * coeffSeminormSeq ξ hξ (k + 1) f :=
    coeffSeminormSeq_lowerOpCLM_le (ξ := ξ) (hξ := hξ) (i := i) (k := k) (f := f)
  -- combine everything
  rw [hsmul]
  have hsum2 :
      ‖(ξ / 2 : ℝ)‖ * coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f + lowerOpCLM ξ i f) ≤
        ‖(ξ / 2 : ℝ)‖ *
          (coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f) +
            coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f)) :=
    mul_le_mul_of_nonneg_left hadd (by positivity)
  refine le_trans hsum2 ?_
  -- substitute the individual bounds and simplify
  have hsum3 :
      ‖(ξ / 2 : ℝ)‖ *
          (coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f) +
            coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f)) ≤
        ‖(ξ / 2 : ℝ)‖ *
          (((Real.sqrt 2 * (2 : ℝ) ^ k) * coeffSeminormSeq ξ hξ (k + 1) f) +
            ((Real.sqrt 2) * coeffSeminormSeq ξ hξ (k + 1) f)) := by
    gcongr
  refine le_trans hsum3 ?_
  -- factor the common term `coeffSeminormSeq ... (k+1) f`
  -- and rewrite the scalar as `Real.sqrt 2 * ((2:ℝ)^k + 1)`.
  have :
      ((Real.sqrt 2 * (2 : ℝ) ^ k) * coeffSeminormSeq ξ hξ (k + 1) f) +
          ((Real.sqrt 2) * coeffSeminormSeq ξ hξ (k + 1) f)
        =
      (Real.sqrt 2 * ((2 : ℝ) ^ k + 1)) * coeffSeminormSeq ξ hξ (k + 1) f := by
    -- purely algebraic
    ring_nf
  -- conclude
  -- rewrite the RHS sum using `this`, then only reassociate scalars
  rw [this]
  -- now both sides are definitionally the same up to associativity/commutativity
  simpa [mul_assoc, mul_left_comm, mul_comm]

lemma coeffSeminormSeq_derivCoordCLM_le (ξ : ℝ) (hξ : ξ ≠ 0) (i : Fin STDimension) (k : ℕ) (f : TestFunction) :
    coeffSeminormSeq ξ hξ k (derivCoordCLM i f) ≤
      (‖(1 / (2 * ξ) : ℝ)‖ * Real.sqrt 2 * ((2 : ℝ) ^ k + 1)) * coeffSeminormSeq ξ hξ (k + 1) f := by
  -- express `derivCoordCLM` via `raiseOpCLM` and `lowerOpCLM`
  have hderiv :
      derivCoordCLM i f = (1 / (2 * ξ)) • (lowerOpCLM ξ i f - raiseOpCLM ξ i f) := by
    -- `lower - raise = (2 * ξ) • deriv`
    have hdiff :
        lowerOpCLM ξ i f - raiseOpCLM ξ i f = (2 * ξ) • derivCoordCLM i f := by
      calc
        lowerOpCLM ξ i f - raiseOpCLM ξ i f
            = ((ξ⁻¹) • mulCoordCLM i f + ξ • derivCoordCLM i f)
                - ((ξ⁻¹) • mulCoordCLM i f - ξ • derivCoordCLM i f) := by
                  simp [raiseOpCLM_apply, lowerOpCLM_apply]
        _ = ((ξ⁻¹) • mulCoordCLM i f + ξ • derivCoordCLM i f)
                - ((ξ⁻¹) • mulCoordCLM i f + (-ξ) • derivCoordCLM i f) := by
                  simp [sub_eq_add_neg, add_assoc]
        _ = (ξ • derivCoordCLM i f) - ((-ξ) • derivCoordCLM i f) := by
                  simp [add_assoc, add_left_comm, add_comm]
        _ = (ξ • derivCoordCLM i f) + (ξ • derivCoordCLM i f) := by
                  simp [sub_eq_add_neg, add_assoc]
        _ = (2 : ℝ) • (ξ • derivCoordCLM i f) := by
                  simpa [two_smul]
        _ = (2 * ξ) • derivCoordCLM i f := by
                  simp [smul_smul, mul_assoc]
    -- cancel scalar
    have hscalar : (1 / (2 * ξ) : ℝ) * (2 * ξ) = 1 := by
      field_simp [hξ]
    -- Multiply `hdiff` by `(1 / (2 * ξ))` and simplify.
    have hsmul := congrArg (fun x : TestFunction => (1 / (2 * ξ)) • x) hdiff
    -- `hsmul` has the form `a • (lower - raise) = a • ((2*ξ) • deriv)`.
    -- Simplify the RHS to `deriv`.
    have hright :
        (1 / (2 * ξ)) • ((2 * ξ) • derivCoordCLM i f) = derivCoordCLM i f := by
      -- `smul_smul` reduces to scalar multiplication by `(1 / (2 * ξ)) * (2 * ξ)`.
      -- In this file, simp often rewrites `1 / (2 * ξ)` as `ξ⁻¹ * 2⁻¹`, so we record a
      -- compatible scalar identity.
      have hscalar' : (ξ⁻¹ * 2⁻¹ * (2 * ξ) : ℝ) = 1 := by
        field_simp [hξ] <;> ring
      calc
        (1 / (2 * ξ)) • ((2 * ξ) • derivCoordCLM i f)
            = ((1 / (2 * ξ) : ℝ) * (2 * ξ)) • derivCoordCLM i f := by
                exact (smul_smul (1 / (2 * ξ)) (2 * ξ) (derivCoordCLM i f))
        _ = derivCoordCLM i f := by
                -- normalize the scalar to the `hscalar'` form and finish
                -- avoid rewriting loops: just cancel `ξ` explicitly
                have : (ξ * ξ⁻¹ : ℝ) = 1 := by
                  simpa [hξ] using (mul_inv_cancel hξ)
                simpa [this, smul_smul, mul_assoc, mul_left_comm, mul_comm]
    -- Conclude, then flip the equality.
    have hfinal :
        (1 / (2 * ξ)) • (lowerOpCLM ξ i f - raiseOpCLM ξ i f) = derivCoordCLM i f := by
      exact (by simpa [sub_eq_add_neg] using hsmul.trans hright)
    exact hfinal.symm

  -- apply seminorm estimates
  have hsmul :
      coeffSeminormSeq ξ hξ k (derivCoordCLM i f) =
        ‖(1 / (2 * ξ) : ℝ)‖ * coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f - raiseOpCLM ξ i f) := by
    have h :=
      (map_smul_eq_mul (coeffSeminormSeq ξ hξ k) (1 / (2 * ξ))
        (lowerOpCLM ξ i f - raiseOpCLM ξ i f))
    calc
      coeffSeminormSeq ξ hξ k (derivCoordCLM i f)
          = coeffSeminormSeq ξ hξ k ((1 / (2 * ξ)) • (lowerOpCLM ξ i f - raiseOpCLM ξ i f)) := by
              rw [hderiv]
        _ = ‖(1 / (2 * ξ) : ℝ)‖ * coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f - raiseOpCLM ξ i f) := by
              simpa using h
  have hsub :
      coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f - raiseOpCLM ξ i f) ≤
        coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f) +
          coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f) :=
    map_sub_le_add (coeffSeminormSeq ξ hξ k) _ _
  have hlo :
      coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f) ≤
        (Real.sqrt 2) * coeffSeminormSeq ξ hξ (k + 1) f :=
    coeffSeminormSeq_lowerOpCLM_le (ξ := ξ) (hξ := hξ) (i := i) (k := k) (f := f)
  have hra :
      coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f) ≤
        (Real.sqrt 2 * (2 : ℝ) ^ k) * coeffSeminormSeq ξ hξ (k + 1) f :=
    coeffSeminormSeq_raiseOpCLM_le (ξ := ξ) (hξ := hξ) (i := i) (k := k) (f := f)
  -- combine
  rw [hsmul]
  have hmul1 :
      ‖(1 / (2 * ξ) : ℝ)‖ * coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f - raiseOpCLM ξ i f) ≤
        ‖(1 / (2 * ξ) : ℝ)‖ *
          (coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f) +
            coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f)) :=
    mul_le_mul_of_nonneg_left hsub (by positivity)
  refine le_trans hmul1 ?_
  have hsum2 :
      ‖(1 / (2 * ξ) : ℝ)‖ *
          (coeffSeminormSeq ξ hξ k (lowerOpCLM ξ i f) +
            coeffSeminormSeq ξ hξ k (raiseOpCLM ξ i f)) ≤
        ‖(1 / (2 * ξ) : ℝ)‖ *
          (((Real.sqrt 2) * coeffSeminormSeq ξ hξ (k + 1) f) +
            ((Real.sqrt 2 * (2 : ℝ) ^ k) * coeffSeminormSeq ξ hξ (k + 1) f)) := by
    gcongr
  refine le_trans hsum2 ?_
  have :
      ((Real.sqrt 2) * coeffSeminormSeq ξ hξ (k + 1) f) +
          ((Real.sqrt 2 * (2 : ℝ) ^ k) * coeffSeminormSeq ξ hξ (k + 1) f)
        =
      (Real.sqrt 2 * ((2 : ℝ) ^ k + 1)) * coeffSeminormSeq ξ hξ (k + 1) f := by
    ring_nf
  rw [this]
  simpa [mul_assoc, mul_left_comm, mul_comm]

end SpaceTimeHermite

end

end PhysLean

