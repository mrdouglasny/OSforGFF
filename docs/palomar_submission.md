# Submitting OSforGFF to the Palomar Registry

For Sergey Cherkis and Anna Mei. Written 2026-08-18.

**Short version.** Sergey built a Comparator Challenge/Solution pair for the registry. It did
not pass. Four things blocked it, and **all four were defects in OSforGFF — none was a problem
with the Challenge, and none was mathematical.** They are now fixed or in review, and
Comparator passes on Sergey's pair with its mathematical content unchanged. The fixes are
worth having whether or not we ever submit: without them, a future Mathlib update could break
our build outright.

---

## 1. Background

Kim Morrison invited us to register the GFF result in the [Palomar
Registry](https://palomar-registry.org) — a public registry of formalized Lean results, not
yet launched publicly, which uses the Lean FRO's **Comparator** to give each entry an
auditable check. We were asked to be early guinea pigs.

A submission has two Lean files:

- **`Challenge.lean`** — a statement of the theorem that a *mathematician* is expected to
  audit. It may import **Mathlib and nothing else**, so it cannot refer to any OSforGFF
  definition. Everything it needs must be restated from scratch.
- **`Solution.lean`** — proves that statement, and may import anything, including OSforGFF.

Comparator exports the Solution, replays it through the Lean kernel, and checks that every
constant the theorem depends on **matches structurally** between the two files. That last
part is the crux: the two files are elaborated in different environments, so anything that
elaborates differently in the two makes them fail to match.

Sergey wrote both files (654 lines of Challenge), plus `comparator.json` and an updated
`formalization.yaml`, on branch
[`cherkis/OSforGFFgeneral@palomar`](https://github.com/cherkis/OSforGFFgeneral/tree/palomar).
He had not run Comparator, which is where this work picked up.

---

## 2. What Sergey's branch got right

Worth stating plainly, because none of the problems below were his:

- The mathematics audits clean. `positiveTimeSet`, the positive-time submodule, `E d`,
  `properTimeCovariance`, `covarianceForm` and all five OS predicates are character-identical
  to the library's. `Challenge.lean` and `Solution.lean` differ only in the import line, the
  docstring, and the proof body.
- The theorem is stated for **all `d ≥ 2`**, not the `d = 4` case Kim suggested — the
  stronger result.
- It includes a pinning clause `Z[f] = exp(−½⟨f,Cf⟩)` with `Z` the genuine characteristic
  functional, which rules out a vacuous witness. (A Dirac measure at 0 gives `Z ≡ 1` and
  fails it.) Palomar's editorial review looks for exactly this; it was already handled.
- `#print axioms` on the Solution's theorem gives `[propext, Classical.choice, Quot.sound]` —
  precisely Palomar's permitted set.
- Every repo-level mechanical requirement passes: all 12 manifest packages on credential-free
  `https://github.com/…` URLs pinned to full 40-character SHAs, no submodules, no LFS, no
  committed build artefacts.

---

## 3. What blocked it

Comparator reports one mismatch at a time, so these surfaced one after another:

| # | Comparator reported | cause | fix |
|---|---|---|---|
| 1 | `timeShift_hasTemperateGrowth` | Challenge and Solution elaborated in different environments | rename `TestFunction` → `SchwartzTestFunction`, so `Solution.lean` can `import Mathlib` too |
| 2 | `timeReflectionLE._proof_3` | our `InnerProductSpace ℝ (SpaceTime d)` shadowing Mathlib's `PiLp.innerProductSpace` | delete the redundant instance |
| 3 | `timeReflection_inner_map` | anonymous instances take auto-generated names derived from the module, so the same declaration became `…_challenge` in one file and `…_solution` in the other | give them explicit names |
| 4 | `heatKernelProfile._proof_1` | our `NeZero d` shadowing Mathlib's `Nat.instNeZeroSucc` **on a literal numeral** | `priority := low` |

Then:

```
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

In each case the *types* agreed and the *proof terms* differed — defeq terms written
differently. For example, with `pp.explicit`:

```
Challenge: @SeminormedAddGroup.toNorm … (@PiLp.seminormedAddCommGroup …)
Solution:  @PiLp.instNorm …
```

Same source text, both correct, structurally distinct.

---

## 4. Why — two kinds of conflict with Mathlib

The obstacle was never that OSforGFF is large. It is that OSforGFF conflicts with Mathlib in
ways we cannot normally see, **because we do not import all of Mathlib**.

### 4.1 A name collision

Mathlib gained a root-level `TestFunction`
(`Mathlib/Analysis/Distribution/TestFunction.lean`). It is a *different space* from ours:

| | ours | Mathlib's |
|---|---|---|
| condition | rapid decay | compact support in an open `Ω` |
| space | 𝒮(ℝᵈ; ℝ) — Schwartz | 𝓓ⁿ(Ω, F) |
| dual | tempered distributions 𝒮' | distributions 𝒟' |

Both sat at the root namespace, so `import Mathlib` followed by `import OSforGFF` failed
outright: *environment already contains 'TestFunction'*. We had not noticed because Mathlib's
`TestFunction` is not in our import closure — but the margin is **one import edge**: exactly
one Mathlib module imports it (`Analysis.Distribution.Distribution`) and we already import
three of its siblings. Mathlib also now ships `Analysis.Distribution.TemperedDistribution`,
which is what `FieldConfiguration` hand-rolls; migrating to it would trigger the collision
immediately.

Schwartz is the right space for us — the GFF characteristic functional is continuous on 𝒮,
Minlos gives a measure on 𝒮', and the OS axioms are stated over tempered distributions. So
the mathematics does not move; only the name does, and Mathlib has the better claim to the
bare one, since unqualified "test function" conventionally means 𝓓.

After the rename the two coexist — which also proves `TestFunction` was the *only* name
collision, since a second would have failed identically.

### 4.2 Instances shadowing Mathlib's — and importing more of Mathlib does not fix these

Five instances re-registered things Mathlib already derives, each proved `by infer_instance`,
each contributing nothing but a competing name that won synthesis inside our library:

```lean
noncomputable instance (d : ℕ) : InnerProductSpace ℝ (SpaceTime d) := by infer_instance
instance : AddCommMonoid (PositiveTimeTestFunction d)  := by infer_instance   -- and 3 variants
```

The sixth is the one to remember:

```lean
instance {d : ℕ} [Fact (2 ≤ d)] : NeZero d := ⟨by have h : 2 ≤ d := Fact.out; omega⟩
```

Keyed on `Fact (2 ≤ d)`, it fires on **concrete numerals** wherever such a `Fact` is in
scope. `NeZero 3` — needed to elaborate the literal `4` in `heatKernelProfile` — resolved
through it rather than through Mathlib's `Nat.instNeZeroSucc`. Numeral literals inside
OSforGFF were carrying a non-standard proof.

None of this is *unsound*: every one of these instances is defeq to Mathlib's, and no build
ever failed. It is wrong in the sense that OSforGFF elaborated terms differently from the
rest of the Mathlib ecosystem — which is invisible until something compares terms
structurally. Comparator is the first thing that ever did.

Both instances date from the `d`-parameterization work of 2026-07-02 and were reasonable to
write at the time: once `d` became a parameter, `NeZero d` is what makes `Fin d` indexing go
through. The reach into numeral elaboration was not foreseeable without a tool that compares
terms structurally. **PR #11** deletes the five redundant instances and gives `NeZero`
`priority := low`, keeping it available where it is genuinely wanted while restoring
Mathlib's resolution everywhere else.

**This is why the work is worth doing regardless of Palomar.** It is what stops a Mathlib
import-graph change from breaking us, and we were one import edge away from exactly that.

---

## 5. Status

| | what | state |
|---|---|---|
| **#8** | CI: `lake build` + guardrails + `leanchecker` on every push and PR | **merged** |
| **#10** | `TestFunction` → `SchwartzTestFunction` (570 sites, 50 files; no mathematical change) | **merged** |
| **#11** | delete 5 redundant instances; `NeZero` named and given `priority := low` | **merged** |
| **#13** | `AXIOM_AUDIT.md` taken from #9, authored to Sergey | **merged** |
| **#9** | Sergey's guardrail-script repair + `AXIOM_AUDIT.md` | **closed** in favour of #13 — see §6 |
| — | naming the 3 anonymous instances in `Challenge.lean`/`Solution.lean` | adopted on Sergey's rebased `palomar` branch |

`main` now requires a PR with both CI checks green. The approval requirement was dropped
because it was unsatisfiable — Michael was the only collaborator and GitHub forbids
self-approval. Sergey and Anna have since been added with write access, so it could be
restored if we want a second pair of eyes on every change.

Branch **`palomar-passing`** is the exact configuration in which Comparator passes.

---

## 6. What is left

**PR #9 — resolved.** Sergey opened it against the two follow-ups from
the #7 review: a repair to `scripts/check-guardrails.sh`, and `AXIOM_AUDIT.md`. It now
conflicts, because #8 fixed the same script defect and merged first. Both diagnosed the same
real bug — the original silently `exit 0`s when its baseline tag is missing, so it reported
success without checking anything. The two fixes:

- Sergey's keeps the diff-vs-baseline behaviour when the tag is present and adds a
  **scan-mode fallback** when it is absent, so the check works in a clone fetched without
  tags.
- #8's makes the check **absolute** — it always scans the current tree, so there is no
  reference point to lose — and additionally strips comments before scanning, excludes the
  off-graph `Legacy/` tree, reports `file:line`, and exits 2 rather than 0 when pointed at
  the wrong directory. #8 keeps the baseline diff as an opt-in attribution report via
  `GUARDRAIL_BASE=<rev>`.

**The script halves do not need reconciling: #8 is a superset.** Everything #9's script does,
#8's does, plus the comment-stripping (a real false positive — the module docstring of
`Guardrails.lean` names both `axiom` and `sorry` in prose) and the `Legacy/` exclusion.

The duplication went both ways: #8 was already open when #9 was opened. The avoidable mistake
was merging #8 without first checking whether an open PR touched the same file.

Resolution: **take `AXIOM_AUDIT.md` from #9, drop its script change.** The audit document is
wanted by project convention and its claims check out against current `main` — zero `axiom`
declarations in the build graph, all six headline theorems present. Done in **#13**, with
authorship kept to Sergey; the one paragraph there describing the source-level check has been
updated to match the script now on `main`. Sergey closed #9 in favour of #13, and has
rebuilt the pair-specific checks on top of the absolute-scan script on his branch.

(A *later* version of Sergey's script, on his `palomar` branch, does add checks specific to
the Challenge/Solution pair — Challenge must carry exactly one `sorry`, Solution none. Those
are genuinely not in #8 and are worth keeping when that branch is reconciled. They are not
part of PR #9.)

**`formalization.yaml` — done.** Sergey has dropped `cs.LO` (Palomar allows one or two arXiv
codes, and the policy says to classify the mathematics rather than the use of Lean) and
changed both OS papers from `type: article` to `paper`. That second one was a real trap: the
*upstream* v0.4 schema describes the field as "article, book, web post, …", so `article`
looks right and Palomar rejects it.

**Rebase — done.** The `palomar` branch is rebased onto current `main`.

**`Challenge` and `Solution` are still not built by anything automatic.** They are `lean_lib`s
outside `@[default_target]`, so plain `lake build` skips them (3863 jobs vs 8742) — and CI
runs plain `lake build` via `lean-action`. Nothing catches it if they break, which matters
since machine-checking is the point. Whichever way §7 is decided, they need to be a default
target or an explicit CI step in whichever repository ends up holding them.

**Run Comparator on Linux with real `landrun`.** Ours used the macOS `fake-landrun` shim,
which preserves the kernel-acceptance and axiom-whitelist guarantees but not the sandbox.
Palomar runs the real thing.

---

## 7. Branch strategy — a question for Sergey

Sergey proposed keeping `main` as-is and a separate long-lived `palomar` branch. Now that the
fixes turn out to live almost entirely in the library — and are worth having anyway — the
case for that is weaker: the library fixes belong on `main`, and what stays branch-specific
is three files.

Palomar supports a third option first-class, and Kim's own example uses it.
`kim-em/erdos-unit-distance-comparator` is a **thin-wrapper repository** around the
substantive `kim-em/erdos-unit-distance`, declared via `repository.substantive_formalization`
(an `owner/repo` id plus a full 40-character commit SHA). An `OSforGFF-comparator` repo would
hold `Challenge.lean`, `Solution.lean`, `comparator.json`, a small `formalization.yaml`, and
a lakefile pinning OSforGFF at a commit. `main` stays as it is, and re-pinning becomes an
explicit act rather than continuous drift. The cost is a second repository to maintain.

---

## 8. A technique we did not need

Before the fourth mismatch was diagnosed it looked as though the Challenge would have to
shrink — 654 lines and ~70 re-declared constants against the 43 lines of Kim's accepted
example, each constant an independent chance to diverge. The idea was to state the OS axioms
as *characterisations* rather than *constructions*: instead of building the Euclidean
pullback as a Schwartz map, quantify over any test function agreeing with it pointwise, with
an existence conjunct so the axiom cannot be read as vacuous.

Worked through for OS2 on branch `palomar-slim`, it does what it claims: 14 declarations and
103 lines collapse to 2 definitions and 13 lines, the Solution still discharges it in a
20-line bridge, and the statement gets *stronger*. **It is not needed** — the library fixes
cleared every mismatch with the Challenge unchanged. It is recorded because it would be
useful if a future Challenge does need shrinking, and because a smaller Challenge is easier
to audit; Palomar warns above 300 lines and 654 draws that warning.

---

## 9. Reproducing the Comparator run

```bash
# lean4export must match the project toolchain (v4.33.0-rc1), not comparator's own
git -C ~/Documents/GitHub/lean4export worktree add /tmp/lean4export-4331 v4.33.0-rc1
(cd /tmp/lean4export-4331 && lake build)

git checkout palomar-passing
lake build Challenge Solution            # NOT plain `lake build` — see §6
COMPARATOR_LANDRUN=~/Documents/GitHub/comparator/scripts/fake-landrun.sh \
COMPARATOR_LEAN4EXPORT=/tmp/lean4export-4331/.lake/build/bin/lean4export \
  lake env ~/Documents/GitHub/comparator/.lake/build/bin/comparator comparator.json
```

`comparator.json` omits `enable_nanoda`, which is **correct** — Palomar policy says the field
may be absent and that Palomar writes its own protected configuration regardless. Older
Comparator binaries reject the omission; add it to a local copy, never to the committed file.

---

## 10. Policy notes

A distillation of what the registry's own policy requires — the two gates, the mechanical
requirements, the six editorial passes, the scoring floor, and the versioning rules — is in
[`palomar_policy_notes.md`](palomar_policy_notes.md). Three things there bear directly on
decisions still open here:

- **The wrapper decision (§7) must be made before the first submission.** Re-registration
  requires the same source repository and Comparator configuration path; a repository transfer
  needs explicit operator review. Registering from `OSforGFF` and moving to a wrapper later is
  not a cheap change of mind.
- **Challenge size (§8) is lower-risk than assumed.** It feeds `auditability`, which is not a
  registry score and may sit at 3 with a warning without blocking acceptance.
- **Notability is the one dimension that mandates rejection below the floor**, and it must be
  *affirmatively established* — a specifically identified credible research audience. Novelty
  is explicitly not required, so the classical nature of the result is fine, but the case for
  the audience has to be made in the narrative rather than left implicit.

---

## 11. Open question for Kim

The Challenge is 654 lines against the 43 of `PALOMAR-2026-08-08-000001`. It is inside the
hard limits (1,000 lines / 100 KiB) and over the advisory warning (300 lines / 32 KiB). Is a
Challenge of this size acceptable for a result of this shape — OS0–OS4 genuinely need the
spacetime, test-function, generating-functional and positive-time apparatus restated — or is
the size itself a signal? §8 describes a technique that would take it to roughly 350 lines if
that matters.
