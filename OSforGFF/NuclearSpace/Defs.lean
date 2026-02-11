import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Group.Completion
import Mathlib.Analysis.Normed.Module.Completion
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Module
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
def IsNuclearMap {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (T : E →L[ℝ] F) : Prop :=
  ∃ (φ : ℕ → (E →L[ℝ] ℝ)) (y : ℕ → F),
    Summable (fun n => ‖φ n‖ * ‖y n‖) ∧
    ∀ x, T x = ∑' n, (φ n x) • y n

namespace IsNuclearMap

section

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]

/-- Post-composition preserves nuclearity. -/
theorem comp_left {T : E →L[ℝ] F} (hT : IsNuclearMap T) (S : F →L[ℝ] G) :
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

omit [CompleteSpace F] in
/-- Pre-composition preserves nuclearity. -/
theorem comp_right {T : F →L[ℝ] G} (hT : IsNuclearMap T) (R : E →L[ℝ] F) :
    IsNuclearMap (T.comp R) := by
  rcases hT with ⟨φ, y, hsum, hrepr⟩
  let φ' : ℕ → (E →L[ℝ] ℝ) := fun n => (φ n).comp R
  refine ⟨φ', y, ?_, ?_⟩
  · have hleφ : ∀ n, ‖φ' n‖ ≤ ‖φ n‖ * ‖R‖ := by
      intro n
      simpa [φ'] using (ContinuousLinearMap.opNorm_comp_le (h := φ n) R)
    have hle : ∀ n, ‖φ' n‖ * ‖y n‖ ≤ ‖R‖ * (‖φ n‖ * ‖y n‖) := by
      intro n
      have hy : 0 ≤ ‖y n‖ := norm_nonneg _
      have hR : 0 ≤ ‖R‖ := norm_nonneg _
      calc
        ‖φ' n‖ * ‖y n‖ ≤ (‖φ n‖ * ‖R‖) * ‖y n‖ := by
          exact mul_le_mul_of_nonneg_right (hleφ n) hy
        _ = ‖R‖ * (‖φ n‖ * ‖y n‖) := by ring
    have hnonneg : ∀ n, 0 ≤ ‖φ' n‖ * ‖y n‖ := fun n => mul_nonneg (norm_nonneg _) (norm_nonneg _)
    have hsum' : Summable (fun n => ‖R‖ * (‖φ n‖ * ‖y n‖)) := hsum.mul_left ‖R‖
    have hle' : ∀ n, ‖φ' n‖ * ‖y n‖ ≤ ‖R‖ * (‖φ n‖ * ‖y n‖) := hle
    exact Summable.of_nonneg_of_le hnonneg hle' hsum'
  · intro x
    simp [φ', ContinuousLinearMap.comp_apply, hrepr (R x)]

end

end IsNuclearMap

section BanachOfSeminorm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The kernel of a seminorm, as a submodule. -/
def seminormKer (p : Seminorm ℝ E) : Submodule ℝ E where
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

lemma mem_seminormKer_iff (p : Seminorm ℝ E) (x : E) :
    x ∈ seminormKer (E := E) p ↔ p x = 0 :=
  Iff.rfl

/-! ### The normed space induced by a seminorm -/

/-- The normed space obtained by quotienting `E` by the kernel of `p`. -/
abbrev QuotBySeminorm (p : Seminorm ℝ E) : Type _ :=
  E ⧸ seminormKer (E := E) p

namespace QuotBySeminorm

variable (p : Seminorm ℝ E)

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
noncomputable def norm : QuotBySeminorm p → ℝ :=
  Quotient.lift (fun x : E => p x) (by
    intro x y hxy
    have hsub : x - y ∈ seminormKer (E := E) p := by
      exact (Submodule.quotientRel_def (p := seminormKer (E := E) p)).1 hxy
    exact seminorm_eq_of_sub_mem_ker (E := E) p hsub)

lemma norm_mk (x : E) :
    norm p (Submodule.Quotient.mk (p := seminormKer (E := E) p) x) = p x := rfl

noncomputable instance instAddGroupNorm : AddGroupNorm (QuotBySeminorm p) where
  toFun := norm p
  map_zero' := by
    have : (0 : QuotBySeminorm p) =
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
        (Submodule.Quotient.mk (p := seminormKer (E := E) p) (x + y) : QuotBySeminorm p) =
          Submodule.Quotient.mk (p := seminormKer (E := E) p) x +
            Submodule.Quotient.mk (p := seminormKer (E := E) p) y := by
      simp
    simpa [norm, hadd] using (map_add_le_add p x y)
  neg' := by
    intro r
    refine Quotient.inductionOn r ?_
    intro x
    have hneg :
        (-Submodule.Quotient.mk (p := seminormKer (E := E) p) x : QuotBySeminorm p) =
          Submodule.Quotient.mk (p := seminormKer (E := E) p) (-x) := by
      simp
    change norm p (Submodule.Quotient.mk (p := seminormKer (E := E) p) (-x)) =
        norm p (Submodule.Quotient.mk (p := seminormKer (E := E) p) x)
    change p (-x) = p x
    exact map_neg_eq_map p x
  eq_zero_of_map_eq_zero' := by
    intro r hr
    refine Quotient.inductionOn r ?_ hr
    intro x hx
    exact (Submodule.Quotient.mk_eq_zero (p := seminormKer (E := E) p) (x := x)).2 hx

noncomputable instance instNormedAddCommGroup : NormedAddCommGroup (QuotBySeminorm p) :=
  AddGroupNorm.toNormedAddCommGroup (instAddGroupNorm (E := E) p)

instance instNormedSpace : NormedSpace ℝ (QuotBySeminorm p) where
  norm_smul_le := by
    intro a x
    refine Quotient.inductionOn x ?_
    intro y
    have hmksmul :
        (a • (Submodule.Quotient.mk (p := seminormKer (E := E) p) y) : QuotBySeminorm p) =
          Submodule.Quotient.mk (p := seminormKer (E := E) p) (a • y) := by
      simp
    change norm p (a • (Submodule.Quotient.mk (p := seminormKer (E := E) p) y)) ≤
        |a| * norm p (Submodule.Quotient.mk (p := seminormKer (E := E) p) y)
    rw [hmksmul]
    have h : p (a • y) = |a| * p y := by
      simpa [Real.norm_eq_abs] using (map_smul_eq_mul p a y)
    simpa [norm_mk] using (le_of_eq h)

end QuotBySeminorm

/-! ### Completion: a Banach space -/

/-- The completion of `E ⧸ ker p`, a Banach space. -/
abbrev BanachOfSeminorm (p : Seminorm ℝ E) : Type _ :=
  UniformSpace.Completion (QuotBySeminorm (E := E) p)

namespace BanachOfSeminorm

variable (p : Seminorm ℝ E)

/-- The canonical continuous linear embedding `E ⧸ ker p → Completion (E ⧸ ker p)`. -/
noncomputable def coeCLM :
    QuotBySeminorm (E := E) p →L[ℝ] BanachOfSeminorm (E := E) p :=
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

variable {p q : Seminorm ℝ E}

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

/-- The induced linear map `E ⧸ ker p →ₗ[ℝ] E ⧸ ker q` when `q ≤ p`. -/
noncomputable def inclₗ (hpq : q ≤ p) :
    QuotBySeminorm (E := E) p →ₗ[ℝ] QuotBySeminorm (E := E) q :=
  (seminormKer (E := E) p).mapQ (seminormKer (E := E) q) (LinearMap.id) (by
    simpa using seminormKer_mono_of_le (E := E) (p := p) (q := q) hpq)

@[simp] lemma inclₗ_mk (hpq : q ≤ p) (x : E) :
    inclₗ (E := E) (p := p) (q := q) hpq
        (Submodule.Quotient.mk (p := seminormKer (E := E) p) x) =
      Submodule.Quotient.mk (p := seminormKer (E := E) q) x := by
  simp [inclₗ]

/-- The induced continuous linear map on quotients when `q ≤ p`. -/
noncomputable def inclCLM (hpq : q ≤ p) :
    QuotBySeminorm (E := E) p →L[ℝ] QuotBySeminorm (E := E) q := by
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

variable {p q : Seminorm ℝ E}

/-- The canonical continuous linear inclusion `BanachOfSeminorm p →L BanachOfSeminorm q` for `q ≤ p`. -/
noncomputable def inclCLM (hpq : q ≤ p) :
    BanachOfSeminorm (E := E) p →L[ℝ] BanachOfSeminorm (E := E) q :=
  let e : QuotBySeminorm (E := E) p →L[ℝ] BanachOfSeminorm (E := E) p :=
    BanachOfSeminorm.coeCLM (E := E) p
  let f0 : QuotBySeminorm (E := E) p →L[ℝ] BanachOfSeminorm (E := E) q :=
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
