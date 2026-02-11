import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.UniformSpace.Completion

/-!
# Nuclear spaces (standard Fréchet-style formulation)

This module starts a more standard nuclear-space development than `OSforGFF/NuclearSpace.lean`
(which is specialized to Hilbertian seminorms and Hilbert–Schmidt-type estimates).

We work in the common (and sufficient for Schwartz space) setting where the topology is generated
by a **countable** family of seminorms `p : ℕ → Seminorm ℝ E`. For each seminorm `p n`, we build a
normed space by quotienting `E` by the kernel `{x | p n x = 0}` and equipping the quotient with
the induced norm, then take the completion to obtain a Banach space; this is the standard "local
Banach space" construction used in nuclearity theory.
-/

open scoped BigOperators

namespace OSforGFF

/-! ## Nuclear operators (Banach-space level) -/

/-- A continuous linear map between normed spaces is **nuclear** if it admits a
representation \(T(x)=\sum_n (\varphi_n(x))\,y_n\) with \(\sum_n \|\varphi_n\|\,\|y_n\|<\infty\). -/
def IsNuclearMap {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (T : E →L[𝕜] F) : Prop :=
  ∃ (φ : ℕ → (E →L[𝕜] 𝕜)) (y : ℕ → F),
    Summable (fun n => ‖φ n‖ * ‖y n‖) ∧
    ∀ x, T x = ∑' n, (φ n x) • y n

namespace IsNuclearMap

section Basic

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

/-- The zero map is nuclear. -/
theorem zero : IsNuclearMap (0 : E →L[𝕜] F) := by
  refine ⟨fun _ => 0, fun _ => (0 : F), ?_, ?_⟩
  · simp
  · intro x
    simp

/-- Post-composition preserves nuclearity. -/
theorem comp_left {T : E →L[𝕜] F} (hT : IsNuclearMap T) (S : F →L[𝕜] G) :
    IsNuclearMap (S.comp T) := by
  rcases hT with ⟨φ, y, hsum, hrepr⟩
  refine ⟨φ, fun n => S (y n), ?_, ?_⟩
  · have hle : ∀ n, ‖φ n‖ * ‖S (y n)‖ ≤ ‖S‖ * (‖φ n‖ * ‖y n‖) := by
      intro n
      have hSy : ‖S (y n)‖ ≤ ‖S‖ * ‖y n‖ := by simpa using (S.le_opNorm (y n))
      have hφ : 0 ≤ ‖φ n‖ := norm_nonneg _
      calc
        ‖φ n‖ * ‖S (y n)‖ ≤ ‖φ n‖ * (‖S‖ * ‖y n‖) := by
          exact mul_le_mul_of_nonneg_left hSy hφ
        _ = ‖S‖ * (‖φ n‖ * ‖y n‖) := by ring
    have hnonneg : ∀ n, 0 ≤ ‖φ n‖ * ‖S (y n)‖ :=
      fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsum' : Summable (fun n => ‖S‖ * (‖φ n‖ * ‖y n‖)) := hsum.mul_left ‖S‖
    exact Summable.of_nonneg_of_le hnonneg hle hsum'
  · intro x
    have hterms_norm : Summable (fun n => ‖(φ n x) • y n‖) := by
      have hle : ∀ n, ‖(φ n x) • y n‖ ≤ ‖x‖ * (‖φ n‖ * ‖y n‖) := by
        intro n
        have hxφ : ‖φ n x‖ ≤ ‖φ n‖ * ‖x‖ := by simpa using (φ n).le_opNorm x
        calc
          ‖(φ n x) • y n‖ = ‖φ n x‖ * ‖y n‖ := by simp [norm_smul]
          _ ≤ (‖φ n‖ * ‖x‖) * ‖y n‖ := by
            exact mul_le_mul_of_nonneg_right hxφ (norm_nonneg _)
          _ = ‖x‖ * (‖φ n‖ * ‖y n‖) := by ring
      have hsumx : Summable (fun n => ‖x‖ * (‖φ n‖ * ‖y n‖)) := hsum.mul_left ‖x‖
      have hnonneg : ∀ n, 0 ≤ ‖(φ n x) • y n‖ := fun n => norm_nonneg _
      exact Summable.of_nonneg_of_le hnonneg hle hsumx
    have hterms : Summable (fun n => (φ n x) • y n) :=
      hterms_norm.of_norm
    calc
      (S.comp T) x = S (∑' n : ℕ, (φ n x) • y n) := by
        simp [ContinuousLinearMap.comp_apply, hrepr x]
      _ = ∑' n : ℕ, S ((φ n x) • y n) := by
        simpa using (ContinuousLinearMap.map_tsum (φ := S) hterms)
      _ = ∑' n : ℕ, (φ n x) • S (y n) := by
        simp [map_smul]

/-- Scalar multiplication preserves nuclearity. -/
theorem smul (c : 𝕜) {T : E →L[𝕜] F} (hT : IsNuclearMap T) :
    IsNuclearMap (c • T) := by
  rcases hT with ⟨φ, y, hsum, hrepr⟩
  refine ⟨φ, fun n => c • y n, ?_, ?_⟩
  · -- summability of `‖φ n‖ * ‖c • y n‖`
    have hle : ∀ n, ‖φ n‖ * ‖c • y n‖ ≤ ‖c‖ * (‖φ n‖ * ‖y n‖) := by
      intro n
      -- This is actually an equality.
      have : ‖φ n‖ * ‖c • y n‖ = ‖c‖ * (‖φ n‖ * ‖y n‖) := by
        calc
          ‖φ n‖ * ‖c • y n‖ = ‖φ n‖ * (‖c‖ * ‖y n‖) := by simp [norm_smul]
          _ = ‖c‖ * (‖φ n‖ * ‖y n‖) := by ring
      exact this.le
    have hnonneg : ∀ n, 0 ≤ ‖φ n‖ * ‖c • y n‖ :=
      fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsum' : Summable (fun n => ‖c‖ * (‖φ n‖ * ‖y n‖)) := hsum.mul_left ‖c‖
    exact Summable.of_nonneg_of_le hnonneg hle hsum'
  · intro x
    -- Move scalar multiplication inside the series.
    have hterms_norm : Summable (fun n => ‖(φ n x) • y n‖) := by
      -- same estimate as in `comp_left`
      have hle : ∀ n, ‖(φ n x) • y n‖ ≤ ‖x‖ * (‖φ n‖ * ‖y n‖) := by
        intro n
        have hxφ : ‖φ n x‖ ≤ ‖φ n‖ * ‖x‖ := by simpa using (φ n).le_opNorm x
        calc
          ‖(φ n x) • y n‖ = ‖φ n x‖ * ‖y n‖ := by simp [norm_smul]
          _ ≤ (‖φ n‖ * ‖x‖) * ‖y n‖ := by
            exact mul_le_mul_of_nonneg_right hxφ (norm_nonneg _)
          _ = ‖x‖ * (‖φ n‖ * ‖y n‖) := by ring
      have hsumx : Summable (fun n => ‖x‖ * (‖φ n‖ * ‖y n‖)) := hsum.mul_left ‖x‖
      have hnonneg : ∀ n, 0 ≤ ‖(φ n x) • y n‖ := fun n => norm_nonneg _
      exact Summable.of_nonneg_of_le hnonneg hle hsumx
    have hterms : Summable (fun n => (φ n x) • y n) :=
      hterms_norm.of_norm
    calc
      (c • T) x = c • (∑' n : ℕ, (φ n x) • y n) := by
        simp [ContinuousLinearMap.smul_apply, hrepr x]
      _ = ∑' n : ℕ, c • ((φ n x) • y n) := by
        -- `tsum` commutes with scalar multiplication.
        symm
        simpa using (tsum_const_smul'' (f := fun n : ℕ => (φ n x) • y n) c)
      _ = ∑' n : ℕ, (φ n x) • (c • y n) := by
        refine tsum_congr ?_
        intro n
        -- commute scalars
        simp [smul_smul, mul_comm]

/-- Addition preserves nuclearity. -/
theorem add {T U : E →L[𝕜] F} (hT : IsNuclearMap T) (hU : IsNuclearMap U) :
    IsNuclearMap (T + U) := by
  classical
  rcases hT with ⟨φ₁, y₁, hsum₁, hrepr₁⟩
  rcases hU with ⟨φ₂, y₂, hsum₂, hrepr₂⟩
  let φ : ℕ → (E →L[𝕜] 𝕜) := fun n => if Even n then φ₁ (Nat.div2 n) else φ₂ (Nat.div2 n)
  let y : ℕ → F := fun n => if Even n then y₁ (Nat.div2 n) else y₂ (Nat.div2 n)
  refine ⟨φ, y, ?_, ?_⟩
  · -- Summability of `‖φ n‖ * ‖y n‖` by even/odd splitting.
    have he : Summable (fun k : ℕ => ‖φ (2 * k)‖ * ‖y (2 * k)‖) := by
      simpa [φ, y] using hsum₁
    have ho : Summable (fun k : ℕ => ‖φ (2 * k + 1)‖ * ‖y (2 * k + 1)‖) := by
      simpa [φ, y] using hsum₂
    exact Summable.even_add_odd he ho
  · intro x
    -- Build the even and odd subsequence sums and combine.
    have hterms₁_norm : Summable (fun n => ‖(φ₁ n x) • y₁ n‖) := by
      -- reuse the standard bound with `hsum₁`
      have hle : ∀ n, ‖(φ₁ n x) • y₁ n‖ ≤ ‖x‖ * (‖φ₁ n‖ * ‖y₁ n‖) := by
        intro n
        have hxφ : ‖φ₁ n x‖ ≤ ‖φ₁ n‖ * ‖x‖ := by simpa using (φ₁ n).le_opNorm x
        calc
          ‖(φ₁ n x) • y₁ n‖ = ‖φ₁ n x‖ * ‖y₁ n‖ := by simp [norm_smul]
          _ ≤ (‖φ₁ n‖ * ‖x‖) * ‖y₁ n‖ := by
            exact mul_le_mul_of_nonneg_right hxφ (norm_nonneg _)
          _ = ‖x‖ * (‖φ₁ n‖ * ‖y₁ n‖) := by ring
      have hsumx : Summable (fun n => ‖x‖ * (‖φ₁ n‖ * ‖y₁ n‖)) := hsum₁.mul_left ‖x‖
      have hnonneg : ∀ n, 0 ≤ ‖(φ₁ n x) • y₁ n‖ := fun n => norm_nonneg _
      exact Summable.of_nonneg_of_le hnonneg hle hsumx
    have hterms₁ : Summable (fun n => (φ₁ n x) • y₁ n) :=
      hterms₁_norm.of_norm
    have hterms₂_norm : Summable (fun n => ‖(φ₂ n x) • y₂ n‖) := by
      have hle : ∀ n, ‖(φ₂ n x) • y₂ n‖ ≤ ‖x‖ * (‖φ₂ n‖ * ‖y₂ n‖) := by
        intro n
        have hxφ : ‖φ₂ n x‖ ≤ ‖φ₂ n‖ * ‖x‖ := by simpa using (φ₂ n).le_opNorm x
        calc
          ‖(φ₂ n x) • y₂ n‖ = ‖φ₂ n x‖ * ‖y₂ n‖ := by simp [norm_smul]
          _ ≤ (‖φ₂ n‖ * ‖x‖) * ‖y₂ n‖ := by
            exact mul_le_mul_of_nonneg_right hxφ (norm_nonneg _)
          _ = ‖x‖ * (‖φ₂ n‖ * ‖y₂ n‖) := by ring
      have hsumx : Summable (fun n => ‖x‖ * (‖φ₂ n‖ * ‖y₂ n‖)) := hsum₂.mul_left ‖x‖
      have hnonneg : ∀ n, 0 ≤ ‖(φ₂ n x) • y₂ n‖ := fun n => norm_nonneg _
      exact Summable.of_nonneg_of_le hnonneg hle hsumx
    have hterms₂ : Summable (fun n => (φ₂ n x) • y₂ n) :=
      hterms₂_norm.of_norm
    -- Define the combined term sequence.
    let a : ℕ → F := fun n => (φ n x) • y n
    have ha_even : HasSum (fun n : ℕ => a (2 * n)) (T x) := by
      -- even terms are exactly the `T` terms
      have : HasSum (fun n : ℕ => (φ₁ n x) • y₁ n) (∑' n : ℕ, (φ₁ n x) • y₁ n) :=
        hterms₁.hasSum
      simpa [a, φ, y, hrepr₁ x] using this
    have ha_odd : HasSum (fun n : ℕ => a (2 * n + 1)) (U x) := by
      have : HasSum (fun n : ℕ => (φ₂ n x) • y₂ n) (∑' n : ℕ, (φ₂ n x) • y₂ n) :=
        hterms₂.hasSum
      simpa [a, φ, y, hrepr₂ x] using this
    have ha : HasSum a (T x + U x) :=
      HasSum.even_add_odd ha_even ha_odd
    -- Conclude by rewriting `T+U` and using the computed `tsum`.
    have : (∑' n : ℕ, a n) = T x + U x := ha.tsum_eq
    simp [a, ContinuousLinearMap.add_apply, this]

end Basic

section CompRight

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [CompleteSpace G]

/-- Pre-composition preserves nuclearity. -/
theorem comp_right {T : F →L[𝕜] G} (hT : IsNuclearMap T) (R : E →L[𝕜] F) :
    IsNuclearMap (T.comp R) := by
  rcases hT with ⟨φ, y, hsum, hrepr⟩
  let φ' : ℕ → (E →L[𝕜] 𝕜) := fun n => (φ n).comp R
  refine ⟨φ', y, ?_, ?_⟩
  · have hleφ : ∀ n, ‖φ' n‖ ≤ ‖φ n‖ * ‖R‖ := by
      intro n
      simpa [φ'] using (ContinuousLinearMap.opNorm_comp_le (h := φ n) R)
    have hle : ∀ n, ‖φ' n‖ * ‖y n‖ ≤ ‖R‖ * (‖φ n‖ * ‖y n‖) := by
      intro n
      have hy : 0 ≤ ‖y n‖ := norm_nonneg _
      calc
        ‖φ' n‖ * ‖y n‖ ≤ (‖φ n‖ * ‖R‖) * ‖y n‖ := by
          exact mul_le_mul_of_nonneg_right (hleφ n) hy
        _ = ‖R‖ * (‖φ n‖ * ‖y n‖) := by ring
    have hnonneg : ∀ n, 0 ≤ ‖φ' n‖ * ‖y n‖ :=
      fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsum' : Summable (fun n => ‖R‖ * (‖φ n‖ * ‖y n‖)) := hsum.mul_left ‖R‖
    exact Summable.of_nonneg_of_le hnonneg hle hsum'
  · intro x
    simp [φ', ContinuousLinearMap.comp_apply, hrepr (R x)]

end CompRight

end IsNuclearMap

section BanachOfSeminorm

variable {𝕜 : Type*} [NormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E]

/-- The kernel of a seminorm, as a submodule. -/
def seminormKer (p : Seminorm 𝕜 E) : Submodule 𝕜 E where
  carrier := { x | p x = 0 }
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    have hx0 : p x = 0 := hx
    have hy0 : p y = 0 := hy
    have hle : p (x + y) ≤ 0 := by
      calc
        p (x + y) ≤ p x + p y := map_add_le_add p x y
        _ = 0 := by simp [hx0, hy0]
    have hge : 0 ≤ p (x + y) := by simp
    exact le_antisymm hle hge
  smul_mem' := by
    intro c x hx
    have hx0 : p x = 0 := hx
    simpa [hx0] using (map_smul_eq_mul p c x)

@[simp] lemma mem_seminormKer_iff (p : Seminorm 𝕜 E) (x : E) :
    x ∈ seminormKer (E := E) p ↔ p x = 0 :=
  Iff.rfl

/-! ### The normed space induced by a seminorm -/

/-- The normed space obtained by quotienting `E` by the kernel of `p`. -/
abbrev QuotBySeminorm (p : Seminorm 𝕜 E) : Type _ :=
  E ⧸ seminormKer (E := E) p

namespace QuotBySeminorm

variable (p : Seminorm 𝕜 E)

lemma seminorm_eq_of_sub_mem_ker {x y : E} (h : x - y ∈ seminormKer (E := E) p) :
    p x = p y := by
  have hxy : p (x - y) = 0 := h
  have hyx : p (y - x) = 0 := by
    have : y - x = -(x - y) := by
      abel_nf
    calc
      p (y - x) = p (-(x - y)) := by
        rw [this]
      _ = p (x - y) := by exact map_neg_eq_map p (x - y)
      _ = 0 := hxy
  have hx_le : p x ≤ p y := by
    calc
      p x = p ((x - y) + y) := by abel_nf
      _ ≤ p (x - y) + p y := by
            simpa [sub_eq_add_neg] using (map_add_le_add p (x - y) y)
      _ = p y := by simp [hxy]
  have hy_le : p y ≤ p x := by
    calc
      p y = p ((y - x) + x) := by abel_nf
      _ ≤ p (y - x) + p x := by
            simpa [sub_eq_add_neg] using (map_add_le_add p (y - x) x)
      _ = p x := by simp [hyx]
  exact le_antisymm hx_le hy_le

/-- The induced norm on `E ⧸ ker p` given by the seminorm `p` on representatives. -/
noncomputable def norm : QuotBySeminorm (E := E) p → ℝ :=
  Quotient.lift (fun x : E => p x) (by
    intro x y hxy
    have hsub : x - y ∈ seminormKer (E := E) p := by
      exact (Submodule.quotientRel_def (p := seminormKer (E := E) p)).1 hxy
    exact seminorm_eq_of_sub_mem_ker (E := E) p hsub)

lemma norm_mk (x : E) :
    norm (E := E) p (Submodule.Quotient.mk (p := seminormKer (E := E) p) x) = p x := rfl

noncomputable instance instAddGroupNorm : AddGroupNorm (QuotBySeminorm (E := E) p) where
  toFun := norm (E := E) p
  map_zero' := by
    have : (0 : QuotBySeminorm (E := E) p) =
        Submodule.Quotient.mk (p := seminormKer (E := E) p) (0 : E) := by
      simp
    rw [this]
    change p (0 : E) = 0
    exact map_zero p
  add_le' := by
    intro r s
    refine Quotient.inductionOn₂ r s ?_
    intro x y
    have hadd :
        (Submodule.Quotient.mk (p := seminormKer (E := E) p) (x + y) :
            QuotBySeminorm (E := E) p) =
          Submodule.Quotient.mk (p := seminormKer (E := E) p) x +
            Submodule.Quotient.mk (p := seminormKer (E := E) p) y := by
      simp
    simpa [norm, hadd] using (map_add_le_add p x y)
  neg' := by
    intro r
    refine Quotient.inductionOn r ?_
    intro x
    have hneg :
        (-Submodule.Quotient.mk (p := seminormKer (E := E) p) x :
            QuotBySeminorm (E := E) p) =
          Submodule.Quotient.mk (p := seminormKer (E := E) p) (-x) := by
      simp
    change norm (E := E) p (Submodule.Quotient.mk (p := seminormKer (E := E) p) (-x)) =
        norm (E := E) p (Submodule.Quotient.mk (p := seminormKer (E := E) p) x)
    change p (-x) = p x
    exact map_neg_eq_map p x
  eq_zero_of_map_eq_zero' := by
    intro r hr
    refine Quotient.inductionOn r ?_ hr
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero (p := seminormKer (E := E) p) (x := x)).2 hx

noncomputable instance instNormedAddCommGroup :
    NormedAddCommGroup (QuotBySeminorm (E := E) p) :=
  AddGroupNorm.toNormedAddCommGroup (instAddGroupNorm (E := E) p)

instance instNormedSpace : NormedSpace 𝕜 (QuotBySeminorm (E := E) p) where
  norm_smul_le := by
    intro a x
    refine Quotient.inductionOn x ?_
    intro y
    have hmksmul :
        (a • (Submodule.Quotient.mk (p := seminormKer (E := E) p) y) :
            QuotBySeminorm (E := E) p) =
          Submodule.Quotient.mk (p := seminormKer (E := E) p) (a • y) := by
      simp
    change norm (E := E) p (a • (Submodule.Quotient.mk (p := seminormKer (E := E) p) y)) ≤
        ‖a‖ * norm (E := E) p (Submodule.Quotient.mk (p := seminormKer (E := E) p) y)
    rw [hmksmul]
    have h : p (a • y) = ‖a‖ * p y := by
      simpa using (map_smul_eq_mul p a y)
    simpa [norm_mk (E := E) (p := p)] using (le_of_eq h)

end QuotBySeminorm

/-! ### Completion: a Banach space -/

/-- The completion of `E ⧸ ker p`, a Banach space. -/
abbrev BanachOfSeminorm (p : Seminorm 𝕜 E) : Type _ :=
  UniformSpace.Completion (QuotBySeminorm (E := E) p)

namespace BanachOfSeminorm

variable (p : Seminorm 𝕜 E)

/-- The canonical continuous linear embedding `E ⧸ ker p → Completion (E ⧸ ker p)`. -/
noncomputable def coeCLM :
    QuotBySeminorm (E := E) p →L[𝕜] BanachOfSeminorm (E := E) p :=
  { toLinearMap :=
      { toFun := fun x => (x : BanachOfSeminorm (E := E) p)
        map_add' := by
          intro x y
          simpa using (UniformSpace.Completion.coe_add x y)
        map_smul' := by
          intro r x
          simp }
    cont := by
      simpa using
        (UniformSpace.Completion.continuous_coe (α := QuotBySeminorm (E := E) p)) }

lemma denseRange_coeCLM :
    DenseRange (coeCLM (E := E) p) := by
  simpa [coeCLM] using
    (UniformSpace.Completion.denseRange_coe (α := QuotBySeminorm (E := E) p))

lemma isUniformInducing_coeCLM :
    IsUniformInducing (coeCLM (E := E) p) := by
  simpa [coeCLM] using
    (UniformSpace.Completion.isUniformInducing_coe (α := QuotBySeminorm (E := E) p))

end BanachOfSeminorm

/-! ### Canonical inclusions for `q ≤ p` (on quotients and on completions) -/

namespace QuotBySeminorm

variable {p q : Seminorm 𝕜 E}

/-- If `q ≤ p`, then `ker p ≤ ker q`. -/
lemma seminormKer_mono_of_le (hpq : q ≤ p) :
    seminormKer (E := E) p ≤ seminormKer (E := E) q := by
  intro x hx
  have hx0 : p x = 0 := hx
  have hle : q x ≤ 0 := by
    have : q x ≤ p x := hpq x
    simpa [hx0] using this
  have hge : 0 ≤ q x := by simp
  exact le_antisymm hle hge

/-- The induced linear map `E ⧸ ker p →ₗ[𝕜] E ⧸ ker q` when `q ≤ p`. -/
noncomputable def inclₗ (hpq : q ≤ p) :
    QuotBySeminorm (E := E) p →ₗ[𝕜] QuotBySeminorm (E := E) q :=
  (seminormKer (E := E) p).mapQ (seminormKer (E := E) q) (LinearMap.id) (by
    simpa using seminormKer_mono_of_le (E := E) (p := p) (q := q) hpq)

@[simp] lemma inclₗ_mk (hpq : q ≤ p) (x : E) :
    inclₗ (E := E) (p := p) (q := q) hpq
        (Submodule.Quotient.mk (p := seminormKer (E := E) p) x) =
      Submodule.Quotient.mk (p := seminormKer (E := E) q) x := by
  simp [inclₗ]

/-- The induced continuous linear map on quotients when `q ≤ p`. -/
noncomputable def inclCLM (hpq : q ≤ p) :
    QuotBySeminorm (E := E) p →L[𝕜] QuotBySeminorm (E := E) q := by
  classical
  refine (inclₗ (E := E) (p := p) (q := q) hpq).mkContinuous 1 ?_
  intro x
  refine Quotient.inductionOn x ?_
  intro y
  change
      QuotBySeminorm.norm (E := E) q
          (inclₗ (E := E) (p := p) (q := q) hpq
            (Submodule.Quotient.mk (p := seminormKer (E := E) p) y))
        ≤ 1 *
          QuotBySeminorm.norm (E := E) p (Submodule.Quotient.mk (p := seminormKer (E := E) p) y)
  simp [inclₗ_mk (E := E) (p := p) (q := q) hpq,
    QuotBySeminorm.norm_mk (E := E) (p := q),
    QuotBySeminorm.norm_mk (E := E) (p := p), hpq y]

end QuotBySeminorm

namespace BanachOfSeminorm

variable {p q : Seminorm 𝕜 E}

/-- The canonical continuous linear inclusion `BanachOfSeminorm p →L BanachOfSeminorm q` for `q ≤ p`. -/
noncomputable def inclCLM (hpq : q ≤ p) :
    BanachOfSeminorm (E := E) p →L[𝕜] BanachOfSeminorm (E := E) q :=
  let e : QuotBySeminorm (E := E) p →L[𝕜] BanachOfSeminorm (E := E) p :=
    BanachOfSeminorm.coeCLM (E := E) p
  let f0 : QuotBySeminorm (E := E) p →L[𝕜] BanachOfSeminorm (E := E) q :=
    (BanachOfSeminorm.coeCLM (E := E) q).comp (QuotBySeminorm.inclCLM (E := E) (p := p) (q := q) hpq)
  f0.extend e

@[simp]
lemma inclCLM_coe (hpq : q ≤ p) (x : QuotBySeminorm (E := E) p) :
    inclCLM (E := E) (p := p) (q := q) hpq (x : BanachOfSeminorm (E := E) p) =
      (QuotBySeminorm.inclCLM (E := E) (p := p) (q := q) hpq x :
        BanachOfSeminorm (E := E) q) := by
  classical
  simpa [inclCLM] using
    (ContinuousLinearMap.extend_eq
      (f := (BanachOfSeminorm.coeCLM (E := E) q).comp
        (QuotBySeminorm.inclCLM (E := E) (p := p) (q := q) hpq))
      (e := BanachOfSeminorm.coeCLM (E := E) p)
      (h_dense := BanachOfSeminorm.denseRange_coeCLM (E := E) (p := p))
      (h_e := BanachOfSeminorm.isUniformInducing_coeCLM (E := E) (p := p))
      x)

end BanachOfSeminorm

end BanachOfSeminorm

end OSforGFF
