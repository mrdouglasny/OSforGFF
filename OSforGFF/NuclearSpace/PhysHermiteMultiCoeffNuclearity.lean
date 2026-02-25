/-
Copyright (c) 2026 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina
-/

import OSforGFF.NuclearSpace.PhysHermiteMultiCoeffSeminorm
import OSforGFF.NuclearSpace.Transport

/-!
# Local-inclusion nuclearity API for multi-index coefficient seminorms

This file provides the dimension-generic analogue of the spacetime wrapper:
if the coefficient-seminorm family is equivalent (in the `Seminorm.IsBounded` sense)
to a monotone family with nuclear local inclusions, then the coefficient family itself has
nuclear local inclusions.

The theorem is intentionally abstract: analytic estimates proving these hypotheses are developed
in subsequent files.
-/

namespace PhysLean

noncomputable section

namespace MultiHermite

open OSforGFF
open scoped ENNReal

/-- Transport nuclear local-inclusion bounds to `coeffSeminormSeqOf` via seminorm-family equivalence.

This is the generic bridge used to decouple analytic coefficient bounds from the nuclearity API. -/
theorem coeffSeminormSeqOf_localNuclear_of_equiv
    (d : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0)
    (hRD :
      ∀ f : TestFunction d, ∀ k : ℕ,
        Memℓp
          (OSforGFF.RapidDecaySeqIndex.weightFun
            (base := OSforGFF.RapidDecaySeqMultiIndex.base_d d) k (coeffSeq d ξ hξ f))
          (2 : ℝ≥0∞))
    {q : ℕ → Seminorm ℝ (TestFunction d)} (hqmono : Monotone q)
    (hb_q_le_coeff :
      Seminorm.IsBounded (coeffSeminormSeqOf d ξ hξ hRD) q
        (LinearMap.id : TestFunction d →ₗ[ℝ] TestFunction d))
    (hb_coeff_le_q :
      Seminorm.IsBounded q (coeffSeminormSeqOf d ξ hξ hRD)
        (LinearMap.id : TestFunction d →ₗ[ℝ] TestFunction d))
    (hqNuclear :
      ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n < m,
        IsNuclearMap
          (BanachOfSeminorm.inclCLM (E := TestFunction d) (p := q m) (q := q n)
            (hqmono (Nat.le_of_lt hnm)))) :
    ∀ n : ℕ, ∃ m : ℕ, ∃ hnm : n < m,
      IsNuclearMap
        (BanachOfSeminorm.inclCLM (E := TestFunction d)
          (p := coeffSeminormSeqOf d ξ hξ hRD m)
          (q := coeffSeminormSeqOf d ξ hξ hRD n)
          ((coeffSeminormSeqOf_mono d ξ hξ hRD) (Nat.le_of_lt hnm))) := by
  intro n
  rcases
      (NuclearSpaceStd.isNuclear_inclCLM_of_isBounded (E := TestFunction d)
        (p := coeffSeminormSeqOf d ξ hξ hRD) (q := q)
        (coeffSeminormSeqOf_mono d ξ hξ hRD) hqmono
        hb_q_le_coeff hb_coeff_le_q hqNuclear n)
    with ⟨m, hnm, hNuc⟩
  refine ⟨m, hnm, ?_⟩
  simpa using hNuc

end MultiHermite

end

end PhysLean
