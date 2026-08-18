# Palomar submission: what blocked it, and what it took

Status: resolved, 2026-08-18. Comparator passes on
[`cherkis/OSforGFFgeneral@palomar`](https://github.com/cherkis/OSforGFFgeneral/tree/palomar)'s
Challenge/Solution pair with **no change to the mathematical content of the Challenge**.

Audience: Sergey Cherkis, Michael Douglas.

---

## 1. Result

```
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

Four things blocked Comparator. **All four were defects in OSforGFF, none in the Challenge.**
Three were the library declaring instances that shadow Mathlib's canonical ones; one was a
name collision with Mathlib. The Challenge stayed 654 lines and was not restructured.

| # | Comparator reported | cause | fix |
|---|---|---|---|
| 1 | `timeShift_hasTemperateGrowth` | Challenge and Solution elaborated in different environments | rename `TestFunction` → `SchwartzTestFunction`, so `Solution.lean` can `import Mathlib` |
| 2 | `timeReflectionLE._proof_3` | our `InnerProductSpace ℝ (SpaceTime d)` shadowing `PiLp.innerProductSpace` | delete the redundant instance |
| 3 | `timeReflection_inner_map` | anonymous instances get module-derived names (`…_challenge` vs `…_solution`) | give them explicit names |
| 4 | `heatKernelProfile._proof_1` | our `NeZero d` shadowing `Nat.instNeZeroSucc` **on a literal numeral** | `priority := low` |

Total: two library files changed (2 insertions, 7 deletions), one library-wide rename, and
three instances given names in the Challenge/Solution pair.

---

## 2. What this says about the library

The framing that turned out to be right: *the obstacle was never that OSforGFF is large. It
was that OSforGFF conflicts with Mathlib in ways we cannot see, because we do not import all
of Mathlib.*

Two distinct kinds of conflict, and only the first fits that description exactly.

**Name collisions.** Mathlib gained a root-level `TestFunction`
(`Mathlib/Analysis/Distribution/TestFunction.lean`) — bundled `n`-times-differentiable maps
with compact support in an open `Ω`, i.e. 𝓓ⁿ(Ω, F), dual to the distributions 𝒟'(Ω). Ours was
the Schwartz space 𝒮(ℝᵈ; ℝ), dual to the tempered distributions 𝒮' that `FieldConfiguration`
is built from. Different spaces, same root-level name, so `import Mathlib` followed by
`import OSforGFF` failed outright. Hidden only because Mathlib's `TestFunction` is not in our
import closure today — and the margin is one import edge: exactly one Mathlib module imports
it (`Analysis.Distribution.Distribution`) and we already import three of its siblings.

After the rename the two coexist. That is also proof `TestFunction` was the *only* name
collision, since a second would have failed the same way.

**Instance shadowing — and importing more of Mathlib does not fix these.** Five instances
re-registered things Mathlib already derives, each proved `by infer_instance`, each
contributing nothing but a competing name that won synthesis inside our library:

```lean
noncomputable instance (d : ℕ) : InnerProductSpace ℝ (SpaceTime d) := by infer_instance
instance : AddCommMonoid (PositiveTimeTestFunction d)  := by infer_instance   -- and 3 variants
```

The sixth is the one worth remembering:

```lean
instance {d : ℕ} [Fact (2 ≤ d)] : NeZero d := ⟨by have h : 2 ≤ d := Fact.out; omega⟩
```

Keyed on `Fact (2 ≤ d)`, it fires on **concrete numerals** wherever such a `Fact` is in
scope. `NeZero 3` — needed to elaborate the literal `4` in `heatKernelProfile` — was
resolving through it rather than through Mathlib's `Nat.instNeZeroSucc`. Numeral literals
inside OSforGFF were carrying a non-standard `NeZero` proof. Nothing else would have
surfaced that.

None of this is *unsound* — every one of these instances is defeq to Mathlib's, and no build
ever failed. It is wrong in the sense that OSforGFF elaborated terms differently from the
rest of the Mathlib ecosystem, which matters the moment anything compares terms structurally.
Comparator is the first thing that ever did.

**Worth having fixed independently of Palomar.** It is what stops a Mathlib import-graph
change from breaking us, and we were one import edge from exactly that.

---

## 3. What was verified

Against `cherkis/OSforGFFgeneral@palomar` (branched from PR #7's head, `83510b1`):

| check | result |
|---|---|
| `lake build` | green |
| `lake build Challenge Solution` | green — Challenge carries exactly one `sorry`, the challenge hole; Solution none |
| `#print axioms` on the Solution's theorem | `[propext, Classical.choice, Quot.sound]` — exactly Palomar's permitted set |
| Challenge import closure | `import Mathlib` only, satisfying CONTRIBUTING §2.4 |
| `comparator.json` | the four required keys, correct `permitted_axioms` |
| repo mechanical requirements | all pass: 12 manifest packages on credential-free `https://github.com/…` URLs pinned to full 40-char SHAs, no submodules, no LFS, no committed build artifacts, LICENSE Apache-2.0 |
| Comparator | **passes** |

The mathematics audit came out clean. `positiveTimeSet`, the positive-time submodule,
`E d`/`Rotation d`, `properTimeCovariance`, `covarianceForm` and all five OS predicates are
character-identical to the library's. `Challenge.lean` and `Solution.lean` differ only in the
import line, the module docstring, and the proof body.

Two decisions in Sergey's branch are better than what was asked for and should be kept:

- The theorem is stated for **all `d ≥ 2`**, not the `d = 4` instance Kim proposed.
- The pinning clause `Z[f] = exp(−½⟨f,Cf⟩)`, with `Z` the genuine characteristic functional
  `∫ e^{i⟨ω,f⟩} dμ`, rules out a vacuous witness — a Dirac measure at 0 would give `Z ≡ 1`
  and fail it. Exactly what Palomar's editorial review looks for, already handled.

---

## 4. Remaining work

**`formalization.yaml`** — Sergey closed the maintainers, relationship and classification gaps
Kim listed. Two mechanical violations remain:

1. `classification.arxiv` has three codes (`hep-th`, `cs.LO`, `math-ph`); Palomar allows
   **one or two**. Drop `cs.LO` — CONTRIBUTING §3.1 says to "classify the mathematical result
   itself, not the use of Lean or AI."
2. Both OS papers carry `type: article`. Palomar's enum is `paper`, `book`, `web discussion`,
   `folklore`, `original-proof`, `other`. A genuine trap: the *upstream* v0.4 schema describes
   the field as "article, book, web post, …", so `article` looks right and Palomar rejects it.

**Challenge and Solution are not in the default build target.** They are `lean_lib`s outside
`@[default_target]`, so plain `lake build` reports 3863 jobs and skips them;
`lake build Challenge Solution` gives 8742. Nothing catches it if they break — which matters,
since machine-checking is the point.

**Rebase.** The branch is based on PR #7's head rather than current `main`.

**Guardrail script conflict.** The branch's `check-guardrails.sh` rewrite and PR #8's both
address the same defect — the original silently `exit 0`s when its baseline tag is missing —
by different routes. Merge them deliberately rather than letting one overwrite the other.

---

## 5. Branch strategy

Sergey raised keeping `main` as-is with a separate `palomar` branch. Now that the fixes turn
out to live almost entirely in the library, and are worth having anyway, the case for a
long-lived divergent branch is weaker still: the library fixes belong on `main`, and what
remains branch-specific is three files.

Palomar supports a third option first-class, and Kim's own example uses it:
`kim-em/erdos-unit-distance-comparator` is a **thin-wrapper repository** wrapping the
substantive `kim-em/erdos-unit-distance`, declared via `repository.substantive_formalization`
(an `owner/repo` id plus a full 40-char commit SHA). A separate `OSforGFF-comparator` repo
would hold `Challenge.lean`, `Solution.lean`, `comparator.json`, a small `formalization.yaml`
and a lakefile pinning OSforGFF. `main` stays as it is; re-pinning becomes an explicit act
rather than continuous drift. The cost is a second repository to keep alive.

---

## 6. The `ChallengeSlim` experiment — recorded, not needed

Before the fourth mismatch was diagnosed it looked as though the Challenge itself would have
to shrink: 654 lines and ~70 re-declared constants against the 43 lines of Kim's accepted
example, with each constant an independent chance to diverge. The proposed remedy was to
state the OS axioms as *characterisations* rather than *constructions* — quantifying over any
test function that agrees pointwise with a pullback, instead of building the pullback as a
Schwartz map — with an existence conjunct so the axiom could not be read as vacuous.

Worked through for OS2 on branch `palomar-slim`, it does what it claims: 14 declarations and
103 lines collapse to 2 definitions and 13 lines, the Solution still discharges it in a
20-line bridge, the axiom footprint stays clean, and the statement gets *stronger* via the
explicit `EuclideanPullbackExists`.

**It is not needed.** The library fixes cleared every mismatch with the Challenge unchanged.
The technique is recorded because it is genuinely useful if a future Challenge does need
shrinking, and because a smaller Challenge is easier to audit — Palomar warns above 300 lines
and 654 draws that warning. But it is optional polish, not a prerequisite, and it should not
gate the submission.

---

## 7. Reproducing

Branch `palomar-passing` is the exact configuration that passes: the rename, the instance
fixes, and Sergey's Challenge/Solution with three anonymous instances named and
`import Mathlib` added to the Solution.

```bash
# lean4export must match the project toolchain (v4.33.0-rc1), not comparator's own
git -C ~/Documents/GitHub/lean4export worktree add /tmp/lean4export-4331 v4.33.0-rc1
(cd /tmp/lean4export-4331 && lake build)

git checkout palomar-passing
lake build Challenge Solution
COMPARATOR_LANDRUN=~/Documents/GitHub/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/tmp/lean4export-4331/.lake/build/bin/lean4export \
  lake env ~/Documents/GitHub/comparator/.lake/build/bin/comparator comparator.json
```

Two notes. `comparator.json` omits `enable_nanoda`, which is **correct** — Palomar policy says
the field may be absent and that Palomar writes its own protected config regardless. Older
Comparator binaries reject the omission; add it to a local copy, not to the committed file.
And `fake-landrun` preserves the kernel-acceptance and axiom-whitelist guarantees but not the
sandbox, so a Linux box with real `landrun` is the stricter check.

---

## 8. Open question for Kim

The Challenge is 654 lines against the 43 of `PALOMAR-2026-08-08-000001`. It is inside the
hard limits (1,000 lines / 100 KiB) and over the advisory warning (300 lines / 32 KiB). Is a
Challenge of this size acceptable for a result of this shape — OS0–OS4 genuinely need the
spacetime, test-function, generating-functional and positive-time apparatus restated — or is
the size itself a signal? §6 describes a technique that would take it to roughly 350 lines if
that matters.
