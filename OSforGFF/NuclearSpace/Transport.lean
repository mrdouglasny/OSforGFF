import Mathlib.Topology.Separation.Hausdorff

import OSforGFF.NuclearSpace.Defs

/-!
# Transport lemmas for standard nuclearity

This file provides infrastructure to **transport** nuclearity of the local Banach inclusions
between *equivalent* countable seminorm families.

Concretely, if `p q : ℕ → Seminorm ℝ E` are monotone and each seminorm in one family is bounded
by a constant times a finite supremum of the other (`Seminorm.IsBounded … LinearMap.id`), then:

- each individual seminorm is bounded by a constant times a **single** seminorm at some index
  (using monotonicity and `max` on finsets);
- the canonical inclusion map `BanachOfSeminorm (p m) → BanachOfSeminorm (p n)` (for `n < m`)
  can be factored through the `q`-levels using the constant-bounded inclusion maps
  `inclCLM_of_le_smul`;
- hence, if the corresponding inclusion between `q`-levels is nuclear, then so is the canonical
  inclusion between the chosen `p`-levels.

This is the key technical bridge needed to replace a “canonical” seminorm sequence (e.g. the
Schwartz diagonal sups) by any other equivalent seminorm sequence that is more convenient for
proving nuclearity.
-/

open scoped BigOperators NNReal

namespace OSforGFF

noncomputable section

namespace WithSeminorms

open scoped BigOperators NNReal

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [AddCommGroup E] [Module 𝕜 E] [TopologicalSpace E]
variable {ι ι' : Type*}
variable {p : ι → Seminorm 𝕜 E} {q : ι' → Seminorm 𝕜 E}

/-- If two seminorm families `p` and `q` generate the same topology on `E` (as `WithSeminorms`),
then the identity map is bounded in the sense `Seminorm.IsBounded p q LinearMap.id`.

This is the “continuous ⇒ bounded” direction for seminorm-generated topologies. -/
theorem isBounded_id (hp : WithSeminorms p) (hq : WithSeminorms q) :
    Seminorm.IsBounded p q (LinearMap.id : E →ₗ[𝕜] E) := by
  intro i
  rcases Seminorm.bound_of_continuous (p := p) (E := E) hp (q i) (hq.continuous_seminorm i) with
    ⟨s, C, _hCne, hle⟩
  exact ⟨s, C, by simpa using hle⟩

end WithSeminorms

namespace Seminorm

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- For a monotone seminorm family `p : ℕ → Seminorm ℝ E`, any finite supremum `s.sup p` is bounded
by a single seminorm `p N` (take `N = max s`). -/
lemma finset_sup_le_of_monotone {p : ℕ → Seminorm ℝ E} (hp : Monotone p) (s : Finset ℕ) :
    ∃ N : ℕ, s.sup p ≤ p N := by
  classical
  by_cases hs : s = ∅
  · refine ⟨0, ?_⟩
    simp [hs]
  · have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.2 hs
    refine ⟨s.max' hne, ?_⟩
    refine Finset.sup_le ?_
    intro i hi
    exact hp (Finset.le_max' s i hi)

/-- If `q` is bounded by `p` (in the `Seminorm.IsBounded` sense) and `p` is monotone, then each `q i`
is bounded by a constant times a *single* `p N`. -/
lemma isBounded_nat_exists_le_smul {p q : ℕ → Seminorm ℝ E} (hp : Monotone p)
    (hb : Seminorm.IsBounded p q (LinearMap.id : E →ₗ[ℝ] E)) :
    ∀ i : ℕ, ∃ N : ℕ, ∃ C : ℝ≥0, q i ≤ C • p N := by
  intro i
  rcases hb i with ⟨s, C, hq⟩
  -- `comp id` is definitional.
  have hq' : q i ≤ C • s.sup p := by
    simpa using hq
  rcases finset_sup_le_of_monotone (E := E) hp s with ⟨N, hN⟩
  refine ⟨N, C, ?_⟩
  intro x
  have hx₁ : q i x ≤ (C • s.sup p) x := hq' x
  have hx₂ : (s.sup p) x ≤ p N x := hN x
  -- multiply by the nonnegative scalar `C`
  have hx₃ : (C : ℝ) * (s.sup p x) ≤ (C : ℝ) * (p N x) :=
    mul_le_mul_of_nonneg_left hx₂ (by exact_mod_cast (zero_le C))
  -- unfold scalar actions and finish
  simpa [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc] using hx₁.trans hx₃

end Seminorm

namespace NuclearSpaceStd

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

variable {p q : ℕ → Seminorm ℝ E}

/-- Transport nuclearity of the `q`-inclusions to nuclearity of the canonical `p`-inclusions,
assuming `p` and `q` bound each other (via finite sups) and are monotone. -/
theorem isNuclear_inclCLM_of_isBounded
    (hpmono : Monotone p) (hqmono : Monotone q)
    (hb_q_le_p : Seminorm.IsBounded p q (LinearMap.id : E →ₗ[ℝ] E))
    (hb_p_le_q : Seminorm.IsBounded q p (LinearMap.id : E →ₗ[ℝ] E))
    (hqNuclear : ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n < m,
      IsNuclearMap
        (BanachOfSeminorm.inclCLM (E := E) (p := q m) (q := q n)
          (hqmono (Nat.le_of_lt hnm)))) :
    ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n < m,
      IsNuclearMap
        (BanachOfSeminorm.inclCLM (E := E) (p := p m) (q := p n)
          (hpmono (Nat.le_of_lt hnm))) := by
  classical
  intro n
  -- 1) bound `p n` by a single `q i`
  rcases (Seminorm.isBounded_nat_exists_le_smul (E := E) hqmono hb_p_le_q n) with ⟨i, C₁, hpn⟩
  -- 2) choose a nuclear inclusion `q j → q i` with `i < j`
  rcases hqNuclear i with ⟨j, hij, hNuc_qji⟩
  -- 3) bound `q j` by a single `p M`
  rcases (Seminorm.isBounded_nat_exists_le_smul (E := E) hpmono hb_q_le_p j) with ⟨M, C₂, hqj⟩
  -- 4) choose `m = max M (n+1)` so that `n < m` and `q j ≤ C₂ • p m`
  let m : ℕ := Nat.max M (n + 1)
  have hnm : n < m := by
    have : n < n + 1 := Nat.lt_succ_self n
    exact lt_of_lt_of_le this (Nat.le_max_right _ _)
  have hMq : q j ≤ C₂ • p m := by
    have hMm : p M ≤ p m := hpmono (Nat.le_max_left _ _)
    -- scale by `C₂` pointwise
    have hMm' : C₂ • p M ≤ C₂ • p m := by
      intro x
      have hx : p M x ≤ p m x := hMm x
      have hx' : (C₂ : ℝ) * (p M x) ≤ (C₂ : ℝ) * (p m x) :=
        mul_le_mul_of_nonneg_left hx (by exact_mod_cast (zero_le C₂))
      simpa [Seminorm.smul_apply, NNReal.smul_def, smul_eq_mul, mul_assoc] using hx'
    exact hqj.trans hMm'
  -- Build the factorization through `q j → q i`.
  let A :
      BanachOfSeminorm (E := E) (p m) →L[ℝ] BanachOfSeminorm (E := E) (q j) :=
    BanachOfSeminorm.inclCLM_of_le_smul (E := E) (p := p m) (q := q j) hMq
  let B :
      BanachOfSeminorm (E := E) (q j) →L[ℝ] BanachOfSeminorm (E := E) (q i) :=
    BanachOfSeminorm.inclCLM (E := E) (p := q j) (q := q i) (hqmono (Nat.le_of_lt hij))
  let C :
      BanachOfSeminorm (E := E) (q i) →L[ℝ] BanachOfSeminorm (E := E) (p n) :=
    BanachOfSeminorm.inclCLM_of_le_smul (E := E) (p := q i) (q := p n) hpn
  have hNuc_B : IsNuclearMap B := by
    -- `hqNuclear i` gives nuclearity for the *canonical* inclusion `q j → q i`.
    -- Our `B` is definitionaly that inclusion.
    simpa [B] using hNuc_qji
  have hNuc_BA : IsNuclearMap (B.comp A) :=
    IsNuclearMap.comp_right (T := B) hNuc_B A
  have hNuc_CBA : IsNuclearMap (C.comp (B.comp A)) :=
    IsNuclearMap.comp_left (T := B.comp A) hNuc_BA C
  -- 5) identify this composite with the canonical inclusion `p m → p n`
  refine ⟨m, hnm, ?_⟩
  -- show: `inclCLM (p m → p n)` equals `C ∘ B ∘ A`, hence it is nuclear.
  have hEq :
      BanachOfSeminorm.inclCLM (E := E) (p := p m) (q := p n)
            (hpmono (Nat.le_of_lt hnm))
        = C.comp (B.comp A) := by
    -- prove equality of the underlying continuous maps on a dense set, then use injectivity
    apply ContinuousLinearMap.coeFn_injective
    -- dense set: range of the quotient embedding into the completion
    have hd : DenseRange (BanachOfSeminorm.coeCLM (E := E) (p := p m)) :=
      BanachOfSeminorm.denseRange_coeCLM (E := E) (p := p m)
    have hs : Dense (Set.range (BanachOfSeminorm.coeCLM (E := E) (p := p m))) := by
      refine dense_iff_closure_eq.2 ?_
      exact (denseRange_iff_closure_range).1 hd
    -- apply `Continuous.ext_on` as functions `Banach(p m) → Banach(p n)`
    refine Continuous.ext_on hs
      (by fun_prop : Continuous (BanachOfSeminorm.inclCLM (E := E) (p := p m) (q := p n)
        (hpmono (Nat.le_of_lt hnm))))
      (by fun_prop : Continuous (C.comp (B.comp A))) ?_
    rintro _ ⟨xq, rfl⟩
    -- Reduce to quotient-level computation; everything is induced by `LinearMap.id`.
    refine Submodule.Quotient.induction_on (p := seminormKer (E := E) (p := p m)) xq ?_
    intro y
    simp [A, B, C,
      BanachOfSeminorm.coeCLM,
      BanachOfSeminorm.inclCLM_coe, BanachOfSeminorm.inclCLM_of_le_smul_coe,
      QuotBySeminorm.inclCLM, QuotBySeminorm.inclCLM_of_le_smul,
      QuotBySeminorm.inclₗ_mk, QuotBySeminorm.inclₗ_of_le_smul_mk]
  -- use the equality to rewrite the nuclearity proof.
  simpa [hEq] using hNuc_CBA

end NuclearSpaceStd

end

end OSforGFF

