/-
Copyright (c) 2025 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Copyright (c) 2026 Sergey A. Cherkis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sergey A. Cherkis, Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Density
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.FiniteMeasureExt
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving

import OSforGFF.Spacetime.Basic

/-!
# Euclidean Group (E d) and Its Actions

Defines the Euclidean group `(E d) = ℝ^d ⋊ O(d)` with action g • x = R(x) + t
on spacetime, and its induced actions on test functions (g • f)(x) = f(g⁻¹ • x).

Key properties: measure preservation (Lebesgue measure is invariant under `(E d)`), temperate growth of
pullbacks (needed for Schwartz space), and continuity of all actions.
Foundation for the OS2 axiom.
-/

open MeasureTheory NNReal ENNReal
open TopologicalSpace Measure

noncomputable section

/- The Euclidean group of `ℝ^d` and its pullback action on test functions, the
symmetry underlying OS2 (Euclidean invariance) for the Lebesgue-measure spacetime. -/

open scoped Real InnerProductSpace SchwartzMap

namespace QFT

variable {d : ℕ}

/-- Orthogonal linear isometries of `ℝ^d`: the group `O(d)`.
LinearIsometry is an orthogonal linear map, ie an element of `O(d)`. -/
abbrev O (d : ℕ) : Type :=
  LinearIsometry (RingHom.id ℝ) (SpaceTime d) (SpaceTime d)

/-!  Euclidean group -/
/-- Euclidean motion = rotation / reflection + translation. `(E d) = ℝ^d ⋊ O(d)`. -/
structure E (d : ℕ) where
  R : (O d)
  t : (SpaceTime d)

/-- Action of g : (E d) on a spacetime point x.
Impliments the pullback map x to Rx+ t -/
def act (g : (E d)) (x : (SpaceTime d)) : (SpaceTime d) := g.R x + g.t

/-act_one, act_mul and act_inv lemmas prove
identity, composition and inverse. They are needed to say Euclidean sym
form a group. This mirrors OS-2's S_j= S_{EJ} -/
@[simp] lemma act_one   (x : (SpaceTime d)) : act ⟨1,0⟩ x = x := by
  simp [act]

@[simp] lemma act_mul   (g h : (E d)) (x : (SpaceTime d)) :
    act ⟨g.R.comp h.R, g.R h.t + g.t⟩ x = g.R (h.R x + h.t) + g.t := by
  simp [act, add_comm, add_left_comm]

@[simp] lemma act_inv (g : (E d)) (x : (SpaceTime d)) :
    act ⟨g.R, -g.R g.t⟩ x = g.R (x - g.t) := by
  -- unfold the two sides and use linearity of g.R
  simp [act, sub_eq_add_neg, map_add, map_neg]
        -- the map_sub lemma is in mathlib
/- Linear-iso helper lemmas are explicitly in Os-2
but are used as a counter part to rotations that preserve the metric and R^-1 R=1-/
open LinearIsometryEquiv

namespace LinearIsometry
/-- Inverse of a linear isometry : we turn the canonical equivalence
    (available in finite dimension) back into a `LinearIsometry`. -/
noncomputable def inv (g : (O d)) : (O d) :=
  ((g.toLinearIsometryEquiv rfl).symm).toLinearIsometry

@[simp] lemma comp_apply (g h : (O d)) (x : (SpaceTime d)) :
    (g.comp h) x = g (h x) := rfl

@[simp] lemma inv_apply (g : (O d)) (x : (SpaceTime d)) :
    (LinearIsometry.inv g) (g x) = x := by
  -- unfold `inv`, then use the standard `symm_apply_apply` lemma
  dsimp [LinearIsometry.inv]
  simpa using
    (LinearIsometryEquiv.symm_apply_apply (g.toLinearIsometryEquiv rfl) x)
@[simp] lemma one_apply (x : (SpaceTime d)) : (1 : (O d)) x = x := rfl

@[simp] lemma one_comp (R : (O d)) : (1 : (O d)).comp R = R := by
  ext x; simp [comp_apply, one_apply]

@[simp] lemma comp_one (R : (O d)) : R.comp (1 : (O d)) = R := by
  ext x; simp [comp_apply, one_apply]

@[simp] lemma inv_comp (R : (O d)) :
    (LinearIsometry.inv R).comp R = 1 := by
  ext x i
  simp [comp_apply, inv_apply, one_apply]
@[simp] lemma comp_inv (R : (O d)) :
    R.comp (LinearIsometry.inv R) = 1 := by
  -- equality of linear-isometries, proved coordinate-wise
  ext x i
  have h : (R.toLinearIsometryEquiv rfl) ((LinearIsometry.inv R) x) = x :=
    LinearIsometryEquiv.apply_symm_apply (R.toLinearIsometryEquiv rfl) x
  simpa [comp_apply, inv_apply, one_apply] using congrArg (fun v : (SpaceTime d) => v i) h

end LinearIsometry

/-(extentionality) Allows Lean to prove equality of Euclidean motions by checking the R and t
components separately—hugely convenient for the group-law proofs. -/
@[ext] lemma E.ext {g h : (E d)} (hR : g.R = h.R) (ht : g.t = h.t) : g = h := by
  cases g; cases h; cases hR; cases ht; rfl

/-!  ##  Group structure on `(E d)`  ----------------------------------------- -/

/- 1.  Primitive instances of group operations
Implements the semidirect-product multiplication in OS-2:
first rotate, then translate the second translation by the first rotation. -/
instance : Mul (E d) where
  mul g h := ⟨g.R.comp h.R, g.R h.t + g.t⟩

instance : One (E d) where
  one := ⟨1, 0⟩

instance : Inv (E d) where
  inv g := ⟨LinearIsometry.inv g.R, -(LinearIsometry.inv g.R) g.t⟩

/-- We need a `Div` instance because `Group` extends `DivInvMonoid`. -/
instance : Div (E d) where
  div g h := g * h⁻¹

/- helper lemmas mirroring (g. h)_R= g_R dot h_r, and
(g.h)_t= g_R h_t+ g_t)-
-/
@[simp] lemma mul_R (g h : (E d)) : (g * h).R = g.R.comp h.R := rfl
@[simp] lemma mul_t (g h : (E d)) : (g * h).t = g.R h.t + g.t := rfl
@[simp] lemma one_R : (1 : (E d)).R = 1 := rfl
@[simp] lemma one_t : (1 : (E d)).t = 0 := rfl
@[simp] lemma inv_R (g : (E d)) : (g⁻¹).R = LinearIsometry.inv g.R := rfl
@[simp] lemma inv_t (g : (E d)) : (g⁻¹).t = -(LinearIsometry.inv g.R) g.t := rfl

/-Provides the formal group demanded by OS-2's statement
“Euclidean transformations define a group.”-/
instance : Group (E d) where
  mul := (· * ·)
  one := (1 : (E d))
  inv := Inv.inv

  -- associativity
  mul_assoc a b c := by
    apply E.ext
    · simp [mul_R, LinearIsometry.comp_assoc]
    · simp [mul_t, add_comm, add_left_comm]

  -- left and right identity
  one_mul a := by
    apply E.ext
    · simp [mul_R, LinearIsometry.one_comp]
    · simp [mul_t, one_t]

  mul_one a := by
    apply E.ext
    · simp [mul_R, LinearIsometry.comp_one]
    · simp [mul_t, one_t]
  inv_mul_cancel a := by
    -- prove  a⁻¹ * a = 1
    apply E.ext
    · simp [mul_R, inv_R, one_R, LinearIsometry.inv_comp]
    · simp [mul_t, inv_t, one_t]

/-theorem ---------------------------------------------

     For all Euclidean motions g,h and every point x ∈ ℝ^d we have
         act (g * h) x  =  act g (act h x).
     In words: the `act` map is a group action of (E d) on spacetime.

     We also prove the inverse law
         act g⁻¹ (act g x) = x.
-/

/-for all Euclidean motions g and h and any point x ∈ ℝ^d, pulling x forward by the product g*h equals pulling by h first and then by g.
This is precisely the group-action law(𝑔ℎ)⁣⋅𝑥=𝑔.(ℎ. 𝑥)(gh)⋅x=g⋅(h⋅x).-/

@[simp] lemma act_mul_general (g h : (E d)) (x : (SpaceTime d)) :
    act (g * h) x = act g (act h x) := by
  -- destructure g and h so Lean can see their components
/-cases on g/h: expands each motion into its components
gR : (O d) the rotation, gt : ℝ^d the translation.
hR, ht likewise. That lets Lean see the literal structure of g*h.-/
  cases g with
  | mk gR gt =>
    cases h with
    | mk hR ht =>
      -- unfold everything; `mul_R`, `mul_t` give the components of g*h
      /-simp does it all:

act unfolds to R x + t.

mul_R, mul_t give formulas for the rotation/translation of g*h.

A handful of commutativity/associativity lemmas reorganise 𝑔𝑅(ℎ𝑅𝑥+ℎ𝑡)+𝑔𝑡gR(hRx+ht)+g
t into the desired form.
→ Goal reduces to reflexive equality, proof finished.-/
      simp [act, mul_R, mul_t, add_comm, add_left_comm]

/-Statement: applying g to x and then applying the inverse motion g⁻¹ returns you to x.
This is the inverse law of a group action.-/
/-Result: we’ve established that act : (E d) → (ℝ^d → ℝ^d) is a homomorphism into the function-composition monoid—exactly what OS-2 needs for its pull-back action on fields.-/

@[simp] lemma act_inv_general (g : (E d)) (x : (SpaceTime d)) :
    act g⁻¹ (act g x) = x := by
  cases g with
  | mk gR gt =>
      -- unfold act, inverse components, then use linearity of gR
      simp [act, inv_R, inv_t, add_comm, add_assoc]
/-Result: confirms that act really is a faithful left action of the Euclidean group; no hidden sign or composition mistakes remain.-/


/-! ### Lebesgue measure is invariant under every Euclidean motion --------- -/

open MeasureTheory
open MeasureTheory

/-- For every rigid motion `g : (E d)`, the push‑forward of Lebesgue measure `μ`
    by the map `x ↦ g • x` is again `μ`.  Equivalently, `act g` is
    measure‑preserving. -/
lemma measurePreserving_act (g : (E d)) :
    MeasurePreserving (fun x : (SpaceTime d) => act g x) (volume : Measure (SpaceTime d)) volume := by
  have rot : MeasurePreserving (fun x : (SpaceTime d) => g.R x) (volume : Measure (SpaceTime d)) volume := by
    simpa using (g.R.toLinearIsometryEquiv rfl).measurePreserving
  have trans : MeasurePreserving (fun x : (SpaceTime d) => x + g.t) (volume : Measure (SpaceTime d)) volume := by
    refine ⟨(continuous_id.add continuous_const).measurable, ?_⟩
    simpa using map_add_right_eq_self (volume : Measure (SpaceTime d)) g.t
  simpa [act, Function.comp_def] using trans.comp rot

-- Temperate-growth helpers for the pullback map
open Function

private lemma contDiff_act_inv (g : (E d)) :
    ContDiff ℝ ⊤ (act g⁻¹) := by
  have h₁ : ContDiff ℝ ⊤ (fun x : (SpaceTime d) => g⁻¹.R x) := g⁻¹.R.contDiff
  have h₂ : ContDiff ℝ ⊤ (fun _ : (SpaceTime d) => g⁻¹.t) := contDiff_const
  unfold act
  exact h₁.add h₂

private lemma fderiv_linear_add_const (L : (SpaceTime d) →L[ℝ] (SpaceTime d)) (c : (SpaceTime d)) (x : (SpaceTime d)) :
    fderiv ℝ (fun y => L y + c) x = fderiv ℝ L x := by
  apply fderiv_add_const

private theorem fderiv_act_inv_eq_linear (g : (E d)) :
  (fun x => fderiv ℝ (act g⁻¹) x) = fun _ => g⁻¹.R.toContinuousLinearMap := by
  ext x v i
  let L := g⁻¹.R.toContinuousLinearMap
  calc (fderiv ℝ (act g⁻¹) x v) i
      = (fderiv ℝ (fun y => L y + g⁻¹.t) x v) i := rfl
      _ = ((fderiv ℝ (fun y => L y + g⁻¹.t) x) v) i := rfl
      _ = ((fderiv ℝ L x) v) i := by rw [fderiv_linear_add_const]
      _ = (L v) i := by rw [ContinuousLinearMap.fderiv]

private theorem fderiv_has_temperate_growth (g : (E d)) :
    Function.HasTemperateGrowth (fun x => fderiv ℝ (act g⁻¹) x) := by
  rw [fderiv_act_inv_eq_linear g]
  exact Function.HasTemperateGrowth.const _

private theorem act_inv_poly_bound (g : (E d)) :
    ∃ k : ℕ, ∃ C : ℝ, ∀ x : (SpaceTime d), ‖act g⁻¹ x‖ ≤ C * (1 + ‖x‖) ^ k := by
  use 1, (1 + ‖g⁻¹.t‖)
  intro x
  have : act g⁻¹ x = g⁻¹.R x + g⁻¹.t := by simp [act]
  rw [this]
  calc ‖g⁻¹.R x + g⁻¹.t‖
      ≤ ‖g⁻¹.R x‖ + ‖g⁻¹.t‖ := norm_add_le _ _
    _ = ‖x‖ + ‖g⁻¹.t‖ := by rw [g⁻¹.R.norm_map x]
    _ ≤ (1 + ‖g⁻¹.t‖) * (1 + ‖x‖)^1 := by
        simp only [pow_one]
        ring_nf
        have h1 : 0 ≤ ‖x‖ := norm_nonneg x
        have h2 : 0 ≤ ‖g⁻¹.t‖ := norm_nonneg _
        linarith [mul_nonneg h2 h1]

 /-! ### Unified Action of Euclidean group on function spaces ---------

    UNIFIED EUCLIDEAN ACTION FRAMEWORK

    This section demonstrates how the same geometric transformation (euclidean_pullback)
    can be used to define Euclidean actions on both test functions and L² functions:

    1. **Common foundation**: All actions are based on the pullback map x ↦ g⁻¹ • x
    2. **Key enabling result**: measurePreserving_act proves this map preserves Lebesgue measure
    3. **Dual routes**:
       - Test functions: Use temperate growth + Schwartz space structure
       - L² functions: Use measure preservation + Lp space structure
    4. **Unified interface**: Both yield continuous linear maps with the same group action laws

    This approach eliminates code duplication and ensures consistency between
    the test function and L² formulations of the Osterwalder-Schrader axioms.
-/

/-- The fundamental pullback map for Euclidean actions.
    This is the geometric transformation x ↦ g⁻¹ • x that underlies
    all Euclidean actions on function spaces. -/
noncomputable def euclidean_pullback (g : (E d)) : (SpaceTime d) → (SpaceTime d) := act g⁻¹

/-- The Euclidean pullback map has temperate growth (needed for Schwartz space actions). -/
lemma euclidean_pullback_temperate_growth (g : (E d)) :
    Function.HasTemperateGrowth (euclidean_pullback g) := by
  -- The map x ↦ g⁻¹.R x + g⁻¹.t is affine (linear isometry + translation)
  unfold euclidean_pullback
  obtain ⟨k, C, hbound⟩ := act_inv_poly_bound g
  exact Function.HasTemperateGrowth.of_fderiv
    (fderiv_has_temperate_growth g)
    ((contDiff_act_inv g).differentiable WithTop.top_ne_zero)
    hbound

/-- The Euclidean pullback map satisfies polynomial growth bounds. -/
lemma euclidean_pullback_polynomial_bounds (g : (E d)) :
    ∃ (k : ℕ) (C : ℝ), ∀ (x : (SpaceTime d)), ‖x‖ ≤ C * (1 + ‖euclidean_pullback g x‖) ^ k := by
  -- Since euclidean_pullback g x = g⁻¹.R x + g⁻¹.t and g⁻¹.R is an isometry:
  use 1, (1 + ‖g⁻¹.t‖)
  intro x
  simp only [pow_one, euclidean_pullback, act]
  have h_iso : ‖g⁻¹.R x‖ = ‖x‖ := g⁻¹.R.norm_map x
  rw [← h_iso]
  have h_ineq : ‖g⁻¹.R x‖ ≤ ‖g⁻¹.R x + g⁻¹.t‖ + ‖g⁻¹.t‖ := norm_le_add_norm_add _ _
  calc ‖g⁻¹.R x‖
      ≤ ‖g⁻¹.R x + g⁻¹.t‖ + ‖g⁻¹.t‖ := h_ineq
    _ ≤ (1 + ‖g⁻¹.t‖) * (1 + ‖g⁻¹.R x + g⁻¹.t‖) := by
        have h1 : 0 ≤ ‖g⁻¹.R x + g⁻¹.t‖ := norm_nonneg _
        have h2 : 0 ≤ ‖g⁻¹.t‖ := norm_nonneg _
        ring_nf
        linarith [mul_nonneg h2 h1]

/-- Action of Euclidean group on test functions via pullback.
    For g ∈ (E d) and f ∈ (SchwartzTestFunctionℂ d), define (g • f)(x) = f(g⁻¹ • x).
    This is the standard pullback action: to evaluate the transformed function
    at x, we evaluate the original function at the inverse-transformed point. -/
noncomputable def euclidean_action (g : (E d)) (f : (SchwartzTestFunctionℂ d)) : (SchwartzTestFunctionℂ d) :=
  SchwartzMap.compCLM (𝕜 := ℂ)
    (hg := euclidean_pullback_temperate_growth g)
    (hg_upper := euclidean_pullback_polynomial_bounds g) f



