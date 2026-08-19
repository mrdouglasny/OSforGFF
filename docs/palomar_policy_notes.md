# Palomar Registry: what the policy actually requires

Working notes distilled from the registry's own policy, so nobody has to re-read 954 lines of
`CONTRIBUTING.md` plus eight review prompts. Read alongside
[`palomar_submission.md`](palomar_submission.md), which is the record of *our* submission.

**Sources**, all in [`PalomarRegistry/PalomarPolicy`](https://github.com/PalomarRegistry/PalomarPolicy)
at commit `24494b2` (2026-08-19): `CONTRIBUTING.md`, `rubric.json`, `prompts/*.md`,
`taxonomies/classification-guide.md`. Entry data is served from `data.palomar-registry.org`
(`recent.json`, `entries/<id>-v<n>.json`) — the website itself is a JS app and returns nothing
useful to a fetcher. The policy is pre-launch and changing; re-check the pinned commit before
relying on any detail below.

---

## 1. Two gates, and the first one proves less than you'd think

**Gate 1 — mechanical verification.** The verifier checks out the commit, discards submitted
build state, materialises the pinned dependencies, compiles the Challenge *separately* against
Lean core plus verified Mathlib/Tau Ceti, records every source file that compilation touched
and rejects anything outside the permitted set, protects the compiled Challenge from
replacement by project build output, writes its own Comparator configuration with NanoDa
enabled outside any writable directory, runs Comparator with no network, and requires every
exported proof to pass Lean's kernel *and* replay through the pinned NanoDa kernel.

What a pass establishes is narrower than it sounds (§5, quoted): it does **not** establish
"that the Challenge says what the metadata claims, that a definition has its ordinary
mathematical meaning, that the metadata is accurate, that the result is novel, or that the
result is interesting." Those are editorial.

**Gate 2 — editorial review.** A language model working through a fixed prompt sequence. No
person reads a submission before a decision. Normally begins only after mechanical
verification passes.

---

## 2. Mechanical requirements, condensed

**Challenge module.** Its *transitive import closure* may contain only Lean core, Mathlib at a
verified revision, or Tau Ceti (which is recorded as a qualified dependency and displays a
warning). No project-specific source anywhere in that closure. Hard limits 100 KiB / 1,000
lines; a mechanical warning above 32 KiB **or** 300 lines. Prefer statements to new
definitions; every definition a compared theorem needs gets a docstring and its ordinary
meaning; state every principal claim and hide no material hypothesis.

**Solution module.** May import anything public. Solution-only dependencies are explicitly
outside the definition-fidelity pass.

**`comparator.json`.** Exactly four required keys — `challenge_module`, `solution_module`,
`theorem_names`, `permitted_axioms` — plus optional `definition_names` and `enable_nanoda`.
No other keys. `permitted_axioms` may contain only `propext`, `Quot.sound`,
`Classical.choice`. `enable_nanoda` is accepted but **non-authoritative**: Palomar ignores the
submitted value and writes its own protected config, so the field may be absent. (Older local
Comparator binaries reject the omission — patch a local copy, never the committed file.)

**Dependencies.** Every Git package in `lake-manifest.json` on a credential-free
`https://github.com/owner/repository` URL, pinned to a full 40-character lowercase SHA. No
submodules, no LFS pointers, no committed compiled artefacts outside `.lake`.

**`formalization.yaml`.** mathlib-initiative v0.4, with Palomar making the
subject-classification, responsible-maintainer and provenance fields mandatory. Hard
requirements: `project.name`; `project.authors`; `project.license` matching the detected SPDX
identifier exactly; `project.responsible_maintainers`; `classification.arxiv` with **one or
two** codes from Palomar's taxonomy snapshot; `classification.msc2020` with one to eight;
`automation.methods` nonempty each with a `method`; `review.status` nonempty; and every source
entry carrying a `title` and a `relationship` from `formalizes | adapts | independently-proves
| background | other`.

**Two traps we hit.** A source `type`, if present, must be one of `paper`, `book`,
`web discussion`, `folklore`, `original-proof`, `other` — the *upstream* v0.4 schema describes
the field as "article, book, web post, …", so `article` looks right and is rejected. And
`classification.arxiv` caps at two codes, so a third (e.g. adding `cs.LO`) fails; the policy
also says to classify the mathematics, not the use of Lean or AI.

**Thin wrappers** (§6.5). A repository existing only to expose another formalisation's
declarations. Provide `repository.substantive_formalization.id` as `owner/repository` and
`.revision` as a full lowercase SHA. Palomar records that underlying repository as the
substantive formalisation, and submitter authorisation must concern *that* project, not the
wrapper.

**Authorisation** (§4). You must be a responsible author or maintainer of the substantive
formalisation, or have approval from one. Explicitly *not* sufficient: write access, shared
ownership, organisation membership, a fork, a transferred repository — "they say what you can
do, not what the work is or whose it is."

---

## 3. Editorial review: six passes

Each returns a bare JSON object with a verdict (`neutral` / `warning` / `failure`), findings
tied to evidence, and only the scores it owns. Every substantive pass must return a coverage
manifest listing every Comparator theorem and then every definition, in configuration order;
an incomplete or reordered manifest is rejected.

| pass | examines | scores owned |
|---|---|---|
| classification | is every arXiv/MSC code substantively plausible | `classification` |
| metadata | clarity, accuracy, completeness of metadata, provenance, narrative | `clarity`, `provenance` |
| statement alignment | does each compared theorem express the claim the prose advertises — definitions, quantifiers, hypotheses, coercions, degenerate cases, scope | `statement_alignment` |
| definition fidelity | do the definitions the statements depend on mean what they claim; auditability of the Challenge closure | `definition_fidelity`, `auditability` |
| literature & notability | literature account and research interest | `notability`, `literature` |
| proof account | *(only if an informal proof account exists)* compares it with the actual Solution proof | — |

Synthesis combines the fixed results; it copies scores exactly and never averages. Outcomes:
`neutral` (no blocking problem), `revision_required` (specific correctable deficiencies),
`rejected` (fundamental failure).

**Findings are public; scores are not.** No reader-visible text may "state, bound, or imply a
score" — even "every score meets the minimum" is forbidden as it bounds all of them. Positive
checks and non-material concerns go to private `internal_notes`, which cannot justify a
decision.

---

## 4. Scoring — where the real bar is

From `rubric.json`: **`minimum_score: 4`**. The registry scores are `statement_alignment`,
`definition_fidelity`, `notability`, `literature`, `clarity`. `mandatory_reject_below_minimum`
lists exactly one: **`notability`**.

The 1–5 anchors put 4 at "thorough, fair, supported by evidence, and correct apart from minor
issues" and 3 at "minimally adequate, but with meaningful limitations or unverified claims".
Critically: *"A score of 4 or 5 requires concrete positive evidence, not merely successful
compilation, populated fields, familiar terminology, or the absence of an obvious
contradiction."* A clean `pass` must reach 4 on every score it owns.

**Notability has its own anchors**, and this is the one that rejects:

- `3`: borderline — paper-worthiness or a credible research audience **not affirmatively
  established**
- `4`: plausibly paper-worthy, with a **specifically identified** credible research audience
- `5`: unusually consequential, beyond a narrow specialist audience

Below 4 is a mandatory reject, "including when a credible research audience or plausible
paper-worthiness has not been affirmatively established." The burden is on the submission.

**Novelty is not required** — the notability prompt says so outright, and forbids inferring
novelty from a missing citation or penalising an original result for lacking a prior source.
A classical result is therefore fine. But "formal verification, effort, length, and polish do
not by themselves establish research interest", so *"this is a large Lean development"* is not
an argument.

**Non-registry scores can sit at 3.** "A non-mandatory dimension may score 3 with a `warn`
verdict and a concrete material finding without blocking acceptance." `auditability` and
`provenance` are scored but are not registry scores.

---

## 5. What this means for OSforGFF

**Challenge size is less dangerous than it looked.** 654 lines draws the >300-line mechanical
warning and feeds `auditability` — which is *not* a registry score and may sit at 3 with a
warning without blocking. So keeping the constructed definitions is defensible. The
"characterise, don't construct" technique would trade that for a risk on a dimension that
*does* block: §1 lists "theories whose definitions have been designed merely to manufacture
the advertised conclusions" as grounds for rejection, and the definition-fidelity prompt hunts
for definitions that "manufacture the conclusion, omit a necessary well-formedness condition,
collapse a reachable case, or otherwise make the claim vacuous". An existential
characterisation invites exactly that scrutiny. Sergey's instinct to keep the definitions is
the lower-risk choice.

**Notability is the one that can reject us, and it needs affirmative evidence.** OS0–OS4 for
the free GFF is classical Glimm–Jaffe, which is fine — novelty isn't required — but the
submission must *affirmatively establish* a specifically identified credible research
audience. That case should be made explicitly in the README and `formalization.yaml` narrative
(constructive/Euclidean QFT; Osterwalder–Schrader reconstruction; the formalisation of QFT
foundations), not left implicit. This is the highest-value remaining editorial work.

**Trust level.** Mathlib-only Challenge imports give `high` trust; ours qualifies. Tau Ceti
would give `qualified`, so avoid it.

**`project.description` is missing from our `formalization.yaml`.** It is not in the upstream
v0.4 schema and is not a mechanical requirement, but Palomar's own template carries it and the
statement-alignment prompt reads it as "a concise, project-wide public abstract" — the thing
that pass assesses for whether it "points, directly or collectively, to the mathematical
subject and principal result families." Absent it, the pass falls back to the README and
docstrings. Adding it is cheap, and it is also the natural place to make the research-audience
case that notability requires.

**The pinning clause already helps.** The statement-alignment pass hunts for statements that
"can be vacuous or materially weaker … than the presented claim". Sergey's
`Z[f] = exp(−½⟨f,Cf⟩)` clause pre-empts the obvious vacuity objection.

---

## 6. Versioning — a one-way door (§9)

Identifiers are `PALOMAR-YYYY-MM-DD-NNNNNN`, the date being acceptance and the serial
sequential from `000001`.

A correction or dependency update **cites the existing identifier and becomes version 2, 3, …**
So re-pinning a wrapper is a first-class supported operation, not a new record. But:

> Automated registration requires the same source repository, selected project path, and
> Comparator configuration path as the current version. … A repository transfer needs
> explicit operator review.

**Therefore the wrapper-versus-main decision must be made before the first submission.**
Registering from `OSforGFF` and later moving to a wrapper is a repository transfer requiring
operator intervention. This is not a workflow preference that can be revisited cheaply.

Also: a source commit already in an identifier's version history cannot be registered again,
and each version separately requires the authorisation declaration of §4 — write access alone
never suffices.

---

## 6a. Submitting as an agent, and how much a submission risks

Push access to the submitted repository is proved one of two ways, and the private submission
record says which.

- **Browser.** A person signs in with GitHub OAuth; the server reads `permissions.push` with
  that token and discards it. One account both *can push* and *identified itself*.
- **Agent** (no browser). Create **a tag at the submitted commit** and **a secret gist
  carrying the same challenge**; Palomar reads both. Creating a ref needs the same write
  access, and the gist supplies an identity, "because a ref records no author and a third
  party cannot ask GitHub who has push."

The agent route is *deliberately the weaker* of the two: it establishes that someone who can
push submitted the repository and that an account named itself, "which are not provably the
same account." The private record carries that distinction. The **published** record does not
— it names no proof route, because it names no submitter either.

Neither route is evidence of authorship. The §4 authorisation relationship is recorded
separately, and write access is explicitly not an answer to it.

**The downside of trying is bounded.** From verification onward, the repository, commit,
submission identifier, verification run and mechanical logs are **public**. But the editorial
review and its outcome stay **private unless the submitter registers a review that identified
no blocking problem** — registration requires explicit consent to the review digest. The
submitter may withdraw from any non-terminal state, and withdrawal leaves no public editorial
outcome. A `revision_required` or `rejected` outcome is not registered, and a corrected commit
enters as a **new submission**, not a new version.

The one irreversible step is registration. Since 2026-08-10 the database is append-only: "a
registration made now is permanent publication history," and a record leaves public view only
by moderator-authorised suppression, which leaves a date-only tombstone.

---

## 6b. `PalomarTemplate` — use it

[`PalomarRegistry/PalomarTemplate`](https://github.com/PalomarRegistry/PalomarTemplate) is a
public best-practice starter: `Challenge.lean`, `Solution.lean`, `comparator.json`, a fully
commented `formalization.yaml` whose placeholder values are *deliberately invalid* until
chosen, a `lakefile.toml`, a nested doc-gen4 project, and CI that builds with `lean-action`
and independently checks the statement with Comparator.

Most useful to us: **`scripts/verify-comparator.sh` runs pinned Comparator, lean4export,
NanoDa and Landrun revisions** against the checked-in `comparator.json`, and
`scripts/landrun-wrapper.sh` "refuses any Comparator request to switch off part of the
sandbox." That is the real-`landrun` run we still owe, already scripted. If we build a wrapper
repository, this is the base to start from rather than assembling one by hand.

Note the template keeps its full proof development *inside* the submission repository — so it
models the all-in-one layout, not the thin wrapper. The wrapper shape is documented separately
in CONTRIBUTING §6.5.

---

## 7. Still unread

`docs/infrastructure.md` (37 KB), `docs/governance.md`, `docs/lawful-requests.md`,
`prompts/materiality.md` and `tests/materiality-cases.json` (which define what counts as a
*material* finding — worth reading before submission), and CONTRIBUTING §8. `specification.md`
has now been read for the lifecycle and proof-route sections; its mechanical-verification and
source-preservation sections have not.
