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

end NuclearSpaceStd

end OSforGFF

