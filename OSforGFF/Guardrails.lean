/-
Build-enforced guardrails.

This file is compiled as part of the library, so `lake build` is the enforcer: the build FAILS
here (via `#guard_msgs`) if any change

  * introduces a new `axiom` reachable from a headline theorem, or
  * lets a `sorry` leak in (surfaces as `sorryAx` in the axiom list), or
  * changes a headline theorem's statement type.

The frozen axiom footprint is exactly Lean's three core axioms (`propext`, `Classical.choice`,
`Quot.sound`); no custom axiom is reachable from the headlines. In particular the dependency
axioms `schwartz_nuclear` / `minlos_theorem` / `differentiable_analyticAt_finDim` are not:
`minlos_theorem` is a proven `theorem` (BochnerMinlos/Minlos/Main.lean), the `schwartz_*`
nuclear axioms live only in BochnerMinlos' `Test/` tree (off the import path), and
`differentiable_analyticAt_finDim` no longer exists. The guards freeze this, so the build also
fails if any of those dependency axioms ever creeps back onto the import path.

Frozen blocks — axiom footprint AND statement type — cover all six headline theorems: the
dimension-generic master theorem, the all-dimensions corollary (`_of_dim`, every `d ≥ 2`), and
the concrete instances `d = 4`, `d = 3`, `d = 2`, and `d = 5`.
-/
import «OSforGFF».OS.Master

-- ── Axiom-footprint guard for the four-dimensional instance ──────────────────
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim4' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim4

-- ── Axiom-footprint guard for the dimension-generic master theorem ───────────
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_generic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_generic

-- ── Goal-type guard: pins the dimension-generic master theorem's statement ────
/-- info: @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_generic : ∀ {d : ℕ} [inst : Fact (2 ≤ d)] (m : ℝ)
  [inst_1 : Fact (0 < m)] [inst_2 : OSforGFF.GFFPropagator d m], SatisfiesAllOS (gaussianFreeField_free m) -/
#guard_msgs in
#check @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_generic

-- ── Goal-type guard: pins the four-dimensional headline's statement ───────────
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim4 : ∀ (m : ℝ) [inst : Fact (0 < m)], SatisfiesAllOS (μ_GFF 4 m) -/
#guard_msgs in
#check @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim4

-- ── Axiom-footprint guard for the three-dimensional instance ─────────────────
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3

-- ── Goal-type guard: pins the three-dimensional headline's statement ─────────
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3 : ∀ (m : ℝ) [inst : Fact (0 < m)], SatisfiesAllOS (μ_GFF 3 m) -/
#guard_msgs in
#check @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim3

-- ── Axiom-footprint guard for the two-dimensional instance ───────────────────
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim2' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim2

-- ── Goal-type guard: pins the two-dimensional headline's statement ───────────
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim2 : ∀ (m : ℝ) [inst : Fact (0 < m)], SatisfiesAllOS (μ_GFF 2 m) -/
#guard_msgs in
#check @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim2

-- ── Axiom-footprint guard for the five-dimensional instance ──────────────────
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim5' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim5

-- ── Goal-type guard: pins the five-dimensional headline's statement ──────────
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim5 : ∀ (m : ℝ) [inst : Fact (0 < m)], SatisfiesAllOS (μ_GFF 5 m) -/
#guard_msgs in
#check @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_dim5

-- ── Axiom-footprint guard for the all-dimensions corollary ───────────────────
/-- info: 'OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim

-- ── Goal-type guard: pins the all-dimensions corollary's statement ───────────
/-- info: OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim : ∀ (d : ℕ) [inst : Fact (2 ≤ d)] (m : ℝ)
  [inst_1 : Fact (0 < m)], SatisfiesAllOS (gaussianFreeField_free m) -/
#guard_msgs in
#check @OSforGFF.gaussianFreeField_satisfies_all_OS_axioms_of_dim
