/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpace.Defs

/-!
# Nuclear spaces (standard, Fréchet-style)

We define a nuclearity hypothesis in the usual **countable-seminorm / local Banach space**
language.  Compared to `OSforGFF/NuclearSpace.lean` (Hilbertian/HS embeddings), this is closer to
the Grothendieck–Pietsch formulation and is the right hypothesis for a principled Bochner–Minlos
pipeline.
-/

namespace OSforGFF

/-- A *standard* (countable-seminorm) nuclearity hypothesis.

There exists a countable family of seminorms `p : ℕ → Seminorm ℝ E` generating the topology, such
that for every `n` there exists `m > n` for which the canonical inclusion between the completed
local Banach spaces `BanachOfSeminorm (p m) → BanachOfSeminorm (p n)` is nuclear.
-/
class NuclearSpaceStd (E : Type*) [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] : Prop where
  nuclear_family :
    ∃ p : ℕ → Seminorm ℝ E,
      ∃ hpmono : Monotone p,
        WithSeminorms p ∧
          ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n < m,
            IsNuclearMap
              (BanachOfSeminorm.inclCLM (E := E)
                (p := p m) (q := p n)
                (hpmono (Nat.le_of_lt hnm)))

namespace NuclearSpaceStd

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [NuclearSpaceStd E]

theorem exists_family :
    ∃ p : ℕ → Seminorm ℝ E,
      ∃ hpmono : Monotone p,
        WithSeminorms p ∧
          ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n < m,
            IsNuclearMap
              (BanachOfSeminorm.inclCLM (E := E)
                (p := p m) (q := p n)
                (hpmono (Nat.le_of_lt hnm))) :=
  NuclearSpaceStd.nuclear_family (E := E)

/-!
### A chosen seminorm family

To avoid destructing `exists_family` repeatedly, we fix (noncomputably) one seminorm family
generating the topology, together with its monotonicity and nuclearity properties.
-/

noncomputable def seminormFamily : ℕ → Seminorm ℝ E := by
  exact Classical.choose (exists_family (E := E))

lemma seminormFamily_spec :
    ∃ hpmono : Monotone (seminormFamily (E := E)),
      WithSeminorms (seminormFamily (E := E)) ∧
        ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n < m,
          IsNuclearMap
            (BanachOfSeminorm.inclCLM (E := E)
              (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
              (hpmono (Nat.le_of_lt hnm))) := by
  simpa [seminormFamily] using (Classical.choose_spec (exists_family (E := E)))

lemma seminormFamily_mono : Monotone (seminormFamily (E := E)) := by
  rcases seminormFamily_spec (E := E) with ⟨hpmono, _⟩
  exact hpmono

lemma seminormFamily_withSeminorms : WithSeminorms (seminormFamily (E := E)) := by
  rcases seminormFamily_spec (E := E) with ⟨_, hp⟩
  exact hp.1

lemma seminormFamily_isNuclearMap (n : ℕ) :
    ∃ hpmono : Monotone (seminormFamily (E := E)),
      ∃ m : ℕ, ∃ hnm : n < m,
        IsNuclearMap
          (BanachOfSeminorm.inclCLM (E := E)
            (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
            (hpmono (Nat.le_of_lt hnm))) := by
  rcases seminormFamily_spec (E := E) with ⟨hpmono, hp⟩
  exact ⟨hpmono, hp.2 n⟩

/-- The local Banach spaces coming from the chosen seminorm family are separable.

This is a standard nuclearity consequence: the inclusion maps are nuclear and have dense range,
hence their codomains are separable. -/
theorem separableSpace_banachOfSeminorm_seminormFamily (n : ℕ) :
    TopologicalSpace.SeparableSpace
      (BanachOfSeminorm (E := E) (seminormFamily (E := E) n)) := by
  classical
  rcases seminormFamily_isNuclearMap (E := E) n with ⟨hpmono, m, hnm, hNuc⟩
  let T :
      BanachOfSeminorm (E := E) (seminormFamily (E := E) m)
        →L[ℝ] BanachOfSeminorm (E := E) (seminormFamily (E := E) n) :=
    BanachOfSeminorm.inclCLM (E := E)
      (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
      (hpmono (Nat.le_of_lt hnm))
  have h_dense : DenseRange T :=
    BanachOfSeminorm.denseRange_inclCLM (E := E)
      (p := seminormFamily (E := E) m) (q := seminormFamily (E := E) n)
      (hpq := hpmono (Nat.le_of_lt hnm))
  -- Apply the general nuclear → separable lemma.
  simpa [T] using (IsNuclearMap.separableSpace_of_denseRange (T := T) hNuc h_dense)

section Consequences

/-!
Basic topological consequences of the existence of a countable seminorm family generating the
topology. These instances are obtained by choosing such a family from `exists_family`.
-/

noncomputable instance : IsTopologicalAddGroup E := by
  exact (seminormFamily_withSeminorms (E := E)).topologicalAddGroup

noncomputable instance : ContinuousSMul ℝ E := by
  exact (seminormFamily_withSeminorms (E := E)).continuousSMul

noncomputable instance : LocallyConvexSpace ℝ E := by
  exact (seminormFamily_withSeminorms (E := E)).toLocallyConvexSpace

noncomputable instance : FirstCountableTopology E := by
  exact (seminormFamily_withSeminorms (E := E)).firstCountableTopology

end Consequences

end NuclearSpaceStd

end OSforGFF
