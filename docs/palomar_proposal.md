# Palomar submission: findings and a proposal

Status: proposal, 2026-08-18. Written after reviewing
[`cherkis/OSforGFFgeneral@palomar`](https://github.com/cherkis/OSforGFFgeneral/tree/palomar)
and running Comparator against it — the step that branch had not yet been through.

Audience: Sergey Cherkis, Michael Douglas. Kim Morrison offered to help prepare the
Comparator files; §6 is the part worth putting to him.

---

## 1. Summary

The `palomar` branch is sound work and the mathematics in it holds up. Comparator does not
pass yet, and the reason is neither a mathematical error nor a defect in the branch: the
Challenge and Solution declare ~70 constants each, and every one of them must match
*structurally* across two independently elaborated environments. Three have failed so far,
each fixed in turn, with no bound on how many remain.

The proposal is to stop peeling mismatches and remove the constants that produce them, by
stating the OS axioms as *characterisations* rather than *constructions*. A worked and
compiled example is in §6: OS2 goes from 14 declarations and 103 lines to 2 definitions and
13 lines, the statement gets stronger rather than weaker, and the Solution still proves it
from the library with a clean axiom footprint.

Two library defects surfaced along the way that are worth fixing regardless of whether we
ever submit to Palomar (§4).

---

## 2. What was verified

Against `cherkis/OSforGFFgeneral@palomar` (branched from PR #7's head, `83510b1`):

| check | result |
|---|---|
| `lake build` | green |
| `lake build Challenge Solution` | green — Challenge carries exactly one `sorry`, the challenge hole; Solution carries none |
| `#print axioms` on the Solution's theorem | `[propext, Classical.choice, Quot.sound]` — exactly Palomar's permitted set |
| Challenge import closure | `import Mathlib` only, satisfying CONTRIBUTING §2.4 |
| `comparator.json` | the four required keys, correct `permitted_axioms` |
| repo mechanical requirements | all pass: 12 manifest packages on credential-free `https://github.com/…` URLs pinned to full 40-char SHAs, no submodules, no LFS, no committed build artifacts, LICENSE Apache-2.0 |

The mathematics audit came out clean. `positiveTimeSet`, the positive-time submodule,
`E d`/`Rotation d`, `properTimeCovariance`, `covarianceForm` and all five OS predicates are
character-identical to the library's. `Challenge.lean` and `Solution.lean` differ *only* in
the import line, the module docstring, and the proof body.

Two design decisions in the branch are better than what was asked for and should be kept:

- The theorem is stated for **all `d ≥ 2`**, not the `d = 4` instance Kim proposed. That is
  the stronger result.
- The pinning clause `Z[f] = exp(−½⟨f,Cf⟩)`, with `Z` the genuine characteristic functional
  `∫ e^{i⟨ω,f⟩} dμ`, rules out a vacuous witness. A Dirac measure at 0 would give `Z ≡ 1`
  and fail it. This is exactly the kind of thing Palomar's editorial review looks for, and
  it is already handled.

---

## 3. The Comparator run

Run with `lean4export` built at `v4.33.0-rc1` to match the project toolchain, and
`fake-landrun` (macOS has no real landrun; this preserves the kernel-acceptance and
axiom-whitelist guarantees but not the sandbox).

One incidental note: `comparator.json` omits `enable_nanoda`, which is **correct** — Palomar
policy says the field may be absent and that Palomar writes its own protected config
regardless. Older Comparator binaries reject the omission. Nothing to change.

The run reaches export and then reports, successively:

```
1.  Const does not match between challenge and target 'Challenge.timeShift_hasTemperateGrowth'
2.  Const does not match between challenge and target 'Challenge.timeReflectionLE._proof_3'
3.  Const does not match between challenge and target 'Challenge.timeReflection_inner_map'
```

Comparator stops at the first mismatch, so these appeared one at a time as each was fixed.

**None of them is a mathematical disagreement.** In each case the types agree and the *proof
terms* differ in how an instance is spelled — defeq terms, structurally distinct. Two
examples, with `pp.explicit`:

```
Challenge: @SeminormedAddGroup.toNorm … (@PiLp.seminormedAddCommGroup …)
Solution:  @PiLp.instNorm …

Challenge: (@PiLp.innerProductSpace Real Real.instRCLike (Fin d) …)
Solution:  (instInnerProductSpaceRealSpaceTime d)
```

The whole file is identical source text. The divergence comes entirely from the two files
being elaborated in different ambient environments.

**All three mismatches live in the three sections that build Schwartz maps out of geometric
transformations** — time translation and time reflection. That is the observation §6 is
built on.

---

## 4. Two library defects, worth fixing regardless

### 4.1 `TestFunction` collides with Mathlib — PR #10

Mathlib gained a root-level `TestFunction`
(`Mathlib/Analysis/Distribution/TestFunction.lean`, Massacci–Dedecker): bundled
`n`-times-differentiable maps with compact support in an open `Ω`, i.e. 𝓓ⁿ(Ω, F), dual to
the distributions 𝒟'(Ω). Ours was the Schwartz space 𝒮(ℝᵈ; ℝ), dual to the tempered
distributions 𝒮' that `FieldConfiguration` is built from. Different spaces, same root-level
name, so this failed outright:

```
import Mathlib
import OSforGFF
-- error: import OSforGFF.Spacetime.Basic failed, environment already contains
--        'TestFunction' from Mathlib.Analysis.Distribution.TestFunction
```

This blocks putting the Challenge and Solution in a common environment. It is also a hazard
independent of Palomar, though **not** an urgent one: Mathlib's `TestFunction` is not
currently in OSforGFF's import closure, so no build breaks today. The margin is one import
edge — exactly one Mathlib module imports it (`Analysis.Distribution.Distribution`), and we
already import three of its siblings (`SchwartzSpace.Deriv`, `SchwartzSpace.Fourier`,
`TemperateGrowth`). Mathlib also now ships `Analysis.Distribution.TemperedDistribution`,
which is precisely what `FieldConfiguration` hand-rolls; migrating to it would trigger the
collision on day one.

Fixed in **PR #10**: `TestFunction` → `SchwartzTestFunction` (with `𝕜`/`ℂ` variants), 570
type-name sites across 50 files plus 9 instance-name sites. `lake build` green at 3863 jobs,
so `Guardrails.lean` still pins all six headline statements and their three-axiom footprint.
No mathematical change. Compounds that merely contain the substring
(`PositiveTimeTestFunction`, `ComplexTestFunction`) are deliberately untouched — already
unambiguous, and prefixing them only makes them unwieldy.

Schwartz is the right space here and should not move: the GFF characteristic functional is
continuous on 𝒮, Minlos delivers a measure on 𝒮', and the OS axioms are stated over tempered
distributions. Mathlib has the better claim to the bare name, since unqualified "test
function" conventionally means 𝓓.

### 4.2 Redundant instances shadowing Mathlib's canonical ones

```lean
noncomputable instance (d : ℕ) : InnerProductSpace ℝ (SpaceTime d) := by infer_instance
```

This re-registers something Mathlib already derives. It adds nothing — it is literally
proved by `infer_instance` — except a competing name that wins synthesis over
`PiLp.innerProductSpace` whenever OSforGFF is imported. The consequence is invisible in
normal use and fatal to structural comparison: terms elaborated inside OSforGFF take a
different instance path from terms elaborated against plain Mathlib. Removing it cleared
comparator mismatch #2, and the library still builds at 3863 jobs.

Four more of the same pattern remain, all in `Spacetime/PositiveTimeTestFunction.lean`:

```lean
instance : AddCommMonoid (PositiveTimeTestFunction d)  := by infer_instance
instance : AddCommGroup  (PositiveTimeTestFunction d)  := by infer_instance
instance : AddCommMonoid (PositiveTimeTestFunctionℂ d) := by infer_instance
instance : AddCommGroup  (PositiveTimeTestFunctionℂ d) := by infer_instance
```

Proposed as a small separate PR.

---

## 5. The structural problem

Kim's own accepted entry, `kim-em/erdos-unit-distance-comparator`, records
`challenge_lines: 43`, `challenge_bytes: 1636`. Ours is 654 lines and 32,137 bytes.

Palomar's thresholds: a mechanical warning above 32 KiB **or** 300 lines; hard limits at
100 KiB and 1,000 lines. So the current file is inside the hard limits and over the warning
line — but the size is a symptom, not the problem. The problem is that ~70 constants must
match structurally across two environments, and each is an independent opportunity to
diverge. Sergey's instinct that "the Palomar format isn't very good for large projects" is
correct as stated; the response is not to fight the format but to shrink what the Challenge
has to declare.

---

## 6. Proposal: characterise, don't construct

**The principle.** Every `def` that *builds* an object is a constant that must match
structurally. Every `∀ … → …` hypothesis that *characterises* the object is free — no
constant, nothing to compare. The Solution can still construct the object and prove it meets
the characterisation, which moves the work out of the audited file and into the unaudited
one. That is the direction Palomar wants: CONTRIBUTING §2.2 asks that "a reader should be
able to identify the exact mathematical result from the Challenge without having to
disentangle the proof development."

### 6.1 Worked example: OS2

**Before** — 103 lines and 14 declarations (`Rotation`, `E`, `act`, `Rotation.inv`, an `Inv`
instance, `euclidean_pullback`, `contDiff_act_inv`, `fderiv_linear_add_const`,
`fderiv_act_inv_eq_linear`, `fderiv_has_temperate_growth`, `act_inv_poly_bound`, two
temperate-growth/antilipschitz lemmas, `euclidean_action`) to support:

```lean
def OS2_EuclideanInvariance (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (g : E d) (f : TestFunctionℂ d),
    GJGeneratingFunctionalℂ dμ_config f =
    GJGeneratingFunctionalℂ dμ_config (euclidean_action g f)
```

**After** — 13 lines, 2 definitions, no supporting apparatus:

```lean
def OS2_EuclideanInvariance (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (R : SpaceTime d ≃ₗᵢ[ℝ] SpaceTime d) (b : SpaceTime d) (f f' : TestFunctionℂ d),
    (∀ x, f' x = f (R.symm (x - b))) →
    GJGeneratingFunctionalℂ dμ_config f = GJGeneratingFunctionalℂ dμ_config f'

def EuclideanPullbackExists (d : ℕ) : Prop :=
  ∀ (R : SpaceTime d ≃ₗᵢ[ℝ] SpaceTime d) (b : SpaceTime d) (f : TestFunctionℂ d),
    ∃ f' : TestFunctionℂ d, ∀ x, f' x = f (R.symm (x - b))
```

Using Mathlib's `LinearIsometryEquiv` supplies the group inverse for free, so `E`,
`Rotation`, `act` and `Rotation.inv` all disappear.

**The vacuity guard matters.** `∀ f', (∀ x, f' x = …) → …` says nothing if no such `f'`
exists, and CONTRIBUTING §2.2 explicitly forbids "weaken[ing] quantifiers" or "replac[ing] a
standard notion with a convenient surrogate". `EuclideanPullbackExists` is added as a
conjunct of the main theorem, so the axiom keeps its full force — and the resulting statement
is in fact *stronger* than the original, which left the existence of the pullback implicit in
its construction.

**Both halves are verified**, not sketched:

- `ChallengeSlim.lean` — 564 lines, `import Mathlib` only, compiles with exactly one `sorry`
  (the hole).
- `SolutionSlim.lean` — compiles and proves it from the library.
  `#print axioms` → `[propext, Classical.choice, Quot.sound]`.

The Solution bridge is 20 lines, of which the only real content is that `LinearIsometry.inv`
of an equivalence's underlying isometry is its inverse:

```lean
have hinv : ∀ (R : SpaceTime d ≃ₗᵢ[ℝ] SpaceTime d) (y),
    QFT.LinearIsometry.inv (R.toLinearIsometry) y = R.symm y :=
  fun R y => by simpa using QFT.LinearIsometry.inv_apply (R.toLinearIsometry) (R.symm y)
```

`SchwartzMap.compCLM_apply` then unfolds the library's constructed action to pointwise form,
and `SchwartzMap.ext` identifies any `f'` satisfying the characterisation with it.

### 6.2 Projected effect on the rest

| section | now | after | note |
|---|---|---|---|
| Euclidean group + action | 103 | 13 | **measured** |
| time reflection + star | 137 | ~20 | keeps `timeReflection` as a plain function; drops the CLM, `≃ₗᵢ`, `Star` instance |
| time translations | 77 | ~12 | same treatment |
| positive-time test functions | 28 | inline | becomes a `tsupport ⊆ {x \| 0 < x₀}` hypothesis, dropping the `Submodule` |
| Schwinger + regularised 2-pt | 66 | ~10 | if `SchwingerTwoPointFunction` can be characterised rather than built from bump mollifiers — **least certain** |

That lands the Challenge around **300–360 lines**, comfortably under the 32 KiB byte
threshold and borderline on the 300-line one. An earlier estimate of 200–250 was too
optimistic; this is the corrected figure.

The line count is not the main argument. The main argument is that **all three known
comparator mismatches live in the sections this removes**, and that what survives is
mostly OS axioms rather than Schwartz-space bookkeeping.

**Risk, stated honestly.** This is not proven to make Comparator pass. It removes the
constants that have failed so far and shrinks the surface on which future mismatches can
occur; it does not prove the remaining surface is clean. The OS2 case is evidence the
pattern works, not a guarantee about the other four.

---

## 7. Smaller items

**`formalization.yaml`** — Sergey closed the maintainers, relationship and classification
gaps Kim listed. Two mechanical violations remain:

1. `classification.arxiv` has three codes (`hep-th`, `cs.LO`, `math-ph`); Palomar allows
   **one or two**. `cs.LO` is the one to drop — CONTRIBUTING §3.1 says to "classify the
   mathematical result itself, not the use of Lean or AI."
2. Both OS papers carry `type: article`. Palomar's enum is `paper`, `book`, `web discussion`,
   `folklore`, `original-proof`, `other`. This is a genuine trap: the *upstream* v0.4 schema
   describes the field as "article, book, web post, …", so `article` looks right and Palomar
   rejects it.

**Challenge and Solution are not in the default build target.** They are `lean_lib`s outside
`@[default_target]`, so plain `lake build` reports 3863 jobs and skips them;
`lake build Challenge Solution` gives 8742. Nothing currently catches it if they break —
which matters, since machine-checking is the whole point. Either add them to the default
target or add them to CI explicitly.

**Rebase.** The branch is based on PR #7's head rather than current `main`, so it predates
the merge commit.

**Guardrail script conflict.** The branch's `check-guardrails.sh` rewrite and the one in
PR #8 both address the same defect — the original silently `exit 0`s when its baseline tag is
missing — by different routes. Sergey's adds a scan-mode fallback and registry-pair checks;
PR #8's makes the check absolute and strips comments before scanning. These should be merged
deliberately rather than letting one overwrite the other.

---

## 8. Branch strategy

Sergey raised keeping `main` as-is and a separate `palomar` branch. A permanently divergent
branch has already drifted after a single merge, and a branch that must be rebased forever is
where the guardrails stop guarding.

Palomar supports a third option first-class, and Kim's own example uses it:
`kim-em/erdos-unit-distance-comparator` is a **thin-wrapper repository** wrapping the
substantive `kim-em/erdos-unit-distance`, declared via
`repository.substantive_formalization` (an `owner/repo` id plus a full 40-char commit SHA).

Recommended: a separate `OSforGFF-comparator` repo holding `Challenge.lean`, `Solution.lean`,
`comparator.json`, a small `formalization.yaml`, and a lakefile depending on OSforGFF at a
pinned commit. `main` stays exactly as it is. Re-pinning to register a newer commit becomes
an explicit act rather than continuous drift. The cost is a second repository to keep alive.

---

## 9. Proposed sequencing

Independent of Palomar, worth doing anyway:

1. Merge PR #10 (the `SchwartzTestFunction` rename).
2. Remove the four remaining `:= by infer_instance` declarations.
3. Resolve the two guardrail-script rewrites into one.

Palomar-specific, in order:

4. Decide branch strategy (§8) before more work lands, since it determines where the files live.
5. Fix the two `formalization.yaml` items (§7).
6. Apply the characterisation pattern to time reflection first — it holds two of the three
   known mismatches — then time translation, then the positive-time submodule.
7. Re-run Comparator after each, and reassess if new mismatches appear outside the sections
   we have rewritten. That would mean the diagnosis in §3 is incomplete.
8. Add Challenge/Solution to the default target or to CI.

---

## 10. Open questions

- **Is registry inclusion worth the remaining effort?** §6 is a real reduction but not a
  guarantee. The honest position is that we cannot yet bound the work.
- **For Kim:** is the characterisation pattern in §6 acceptable to Palomar's editorial
  review, given the explicit existence conjunct? It trades a constructed object in the
  Challenge for a quantified hypothesis plus an existence claim. We read that as strictly
  stronger, but it is exactly the kind of reformulation §2.2 warns about, and it would be
  better to hear that before rewriting five axioms rather than after.
- **Also for Kim:** with a 43-line reference example, is a ~350-line Challenge for a result
  of this shape acceptable in principle, or is that itself a signal that the result is not a
  good registry fit?

---

## Reproducing the Comparator run

```bash
# lean4export must match the project toolchain (v4.33.0-rc1), not comparator's own
git -C ~/Documents/GitHub/lean4export worktree add /tmp/lean4export-4331 v4.33.0-rc1
(cd /tmp/lean4export-4331 && lake build)

cd <OSforGFF>
lake build Challenge Solution
COMPARATOR_LANDRUN=~/Documents/GitHub/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/tmp/lean4export-4331/.lake/build/bin/lean4export \
  lake env ~/Documents/GitHub/comparator/.lake/build/bin/comparator comparator.json
```

Older Comparator binaries require `enable_nanoda` in the config; add it to a local copy
rather than to the committed `comparator.json`, which is correct as it stands.
