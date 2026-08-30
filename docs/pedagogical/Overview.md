# The Osterwalder–Schrader Axioms for the Free Field: A Reader's Index

*A pedagogical map of the six-part OS verification for the unified, dimension-generic
Gaussian Free Field (every $d \ge 2$). Written for a reader who knows Euclidean QFT
and functional integrals but not Lean: the mathematics leads, and the Lean names in
`monospace` are just clickable anchors into the formalization that you can ignore.*

The claim being proved is the one every constructive field theorist wants: **the free,
massive Gaussian field is a genuine Euclidean quantum field theory** — its Euclidean
correlation functions satisfy the Osterwalder–Schrader axioms, hence (by OS
reconstruction) come from a relativistic QFT with a positive-energy Hamiltonian and a
unique vacuum. The five OS axioms are the exact hypotheses of that reconstruction
theorem.

---

## The objects (a 60-second dictionary)

Everything below is phrased in terms of a handful of objects. If you read only one
section, read this one.

- **Field configuration** $\omega$ — a *tempered distribution*, $\omega \in
  \mathscr{S}'(\mathbb{R}^d)$. This is a "random field": not a function, but something you
  can integrate against smooth test functions. The set of all $\omega$ is the sample
  space.
- **Test function** $f$ — a Schwartz function, $f \in \mathscr{S}(\mathbb{R}^d)$ (smooth,
  rapidly decaying). Real for observables; complex ($f \in \mathscr{S}(\mathbb{R}^d,
  \mathbb{C})$) where noted.
- **Smeared field** $\varphi(f) := \langle \omega, f\rangle = \omega(f)$ — the field
  "tested against" $f$, morally $\int \omega(x)\,f(x)\,d^dx$. For a *fixed* $f$ this is a
  **random variable** on the probability space $(\mathscr{S}', \mu)$. *This is the meaning
  of $\varphi$ everywhere in these notes* — so $\varphi(\theta f_j)$ below is just the
  field smeared against the reflected test function $\theta f_j$.
- **The measure** $\mu \equiv \mu_{\mathrm{GFF}}\,d\,m$ — the mean-zero Gaussian
  probability measure on $\mathscr{S}'(\mathbb{R}^d)$ with covariance $C$, constructed
  from $C$ by the Minlos theorem (`Measure/Construct.lean`). Expectations $\mathbb{E}$ are
  against $\mu$.
- **Covariance / propagator** $C = (-\Delta + m^2)^{-1}$ — the two-point function,
  $\mathbb{E}\big[\varphi(f)\,\varphi(g)\big] = \langle f, C g\rangle = \iint f(x)\,
  C(x-y)\,g(y)$, with momentum-space symbol $\widehat{C}(k) = 1/(\lvert k\rvert^2 + m^2)$.
  *Everything* in the proof is a statement about this one object. (The Lean code carries
  an explicit $(2\pi)^2$ from its Fourier convention; we suppress it here.)
- **Generating (characteristic) functional** $Z[J] := \mathbb{E}\big[e^{\,i\varphi(J)}\big]$.
  Because $\mu$ is Gaussian,
  $$Z[J] \;=\; \exp\!\Big(-\tfrac12\,\langle J, C J\rangle\Big). \tag{$\star$}$$
  Formula $(\star)$ is the hinge of the entire development — read every axiom as "some
  property of $C$, seen through $(\star)$."
- **Time reflection** $\theta$ and **positive time** — writing $x = (x_0, \bar x)$ with
  time $x_0 \in \mathbb{R}$ and space $\bar x \in \mathbb{R}^{d-1}$, $(\theta f)(x_0, \bar
  x) = f(-x_0, \bar x)$; a **positive-time** test function is supported in $\{x_0 > 0\}$.
  The lower bound $d \ge 2$ is exactly what makes this time/space split possible.

---

## What "satisfies all OS axioms" means

In Lean the target is `SatisfiesAllOS (μ_GFF d m)`: a record of the five axioms, with OS4
split into its clustering and ergodicity halves ([`OS/Axioms.lean:195`](../../OSforGFF/OS/Axioms.lean#L195)):

```lean
structure SatisfiesAllOS (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop where
  os0            : OS0_Analyticity dμ_config          -- Z is entire in the sources
  os1            : OS1_Regularity dμ_config            -- Z has tempered growth
  os2            : OS2_EuclideanInvariance dμ_config   -- Z is E(d)-invariant
  os3            : OS3_ReflectionPositivity dμ_config  -- reflection positivity
  os4_clustering : OS4_Clustering dμ_config            -- correlations factorize at large separation
  os4_ergodicity : OS4_Ergodicity dμ_config            -- time averages converge to the mean
```

`OS/Master.lean` assembles these six fields, each from one dedicated theorem, and exports
**six headline theorems**: the dimension-generic master
`gaussianFreeField_satisfies_all_OS_axioms_generic` for any $d \ge 2$
([`Master.lean:61`](../../OSforGFF/OS/Master.lean#L61)); the all-dimensions corollary
`..._of_dim` ([`:80`](../../OSforGFF/OS/Master.lean#L80)); and the four concrete instances
$d=4$ ([`:106`](../../OSforGFF/OS/Master.lean#L106)),
$d=3$ Yukawa ([`:97`](../../OSforGFF/OS/Master.lean#L97)),
$d=2$ $K_0$ ([`:90`](../../OSforGFF/OS/Master.lean#L90)),
$d=5$ $K_{3/2}$ ([`:113`](../../OSforGFF/OS/Master.lean#L113)). All six close with only
Lean's three core axioms — no extra assumptions.

The table below is a **navigation aid** (skip it if you don't want to open the source):
which result proves each field, and where.

| Field | Proved by | Where |
|---|---|---|
| `os0` | `gaussianFreeField_satisfies_OS0` | [`OS0_Analyticity.lean:659`](../../OSforGFF/OS/OS0_Analyticity.lean#L659) |
| `os1` | `gaussianFreeField_satisfies_OS1` | [`OS1_Regularity.lean:404`](../../OSforGFF/OS/OS1_Regularity.lean#L404) |
| `os2` | `gaussian_satisfies_OS2` ∘ `CovarianceEuclideanInvariantℂ_μ_GFF` | [`GaussianFreeField.lean:62`](../../OSforGFF/Measure/GaussianFreeField.lean#L62) · [`OS2_Invariance.lean:152`](../../OSforGFF/OS/OS2_Invariance.lean#L152) |
| `os3` | `gaussianFreeField_OS3` | [`OS3_ReflectionPositivity.lean:989`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L989) |
| `os4_clustering` | `gaussianFreeField_satisfies_OS4` | [`OS4_Clustering.lean:440`](../../OSforGFF/OS/OS4_Clustering.lean#L440) |
| `os4_ergodicity` | `OS4_PolynomialClustering_implies_OS4_Ergodicity` (at rate $\alpha=6$, from [`OS4_Clustering.lean:576`](../../OSforGFF/OS/OS4_Clustering.lean#L576)) | [`OS4_Ergodicity.lean:1301`](../../OSforGFF/OS/OS4_Ergodicity.lean#L1301) |

The rest of this note walks the axioms **heaviest first by proof size** — OS3, OS4, OS0,
OS1, OS2 — but be warned: *proof size is not mathematical depth*. The section
["Length is not depth"](#length-is-not-depth-what-is-hard-mathematics-and-what-is-hard-bookkeeping)
sorts them the other way, by how much genuine mathematics each one needs.

---

## OS3 — Reflection positivity

**The most elaborate axiom by a wide margin: $\approx 6750$ lines across four files** — more
than the other four combined.

**What it says (physics).** Reflection positivity is the Euclidean shadow of unitarity: it
is *exactly* the positivity that lets OS reconstruction build a Hilbert space of states
with an inner product $\langle \Theta A, A\rangle \ge 0$ and a self-adjoint Hamiltonian
$H \ge 0$. Concretely, for positive-time test functions $f_1, \dots, f_n$ the matrix
$$M_{jk} \;=\; \mathbb{E}\Big[\,\overline{e^{\,i\varphi(f_j)}}\;e^{\,i\varphi(f_k)}\,\Big]
\;=\; \mathbb{E}\Big[\,e^{\,i\varphi(\theta f_j)}\,e^{\,i\varphi(f_k)}\,\Big] \tag{RP}$$
must be positive semidefinite — where $\varphi(\theta f_j)$ is the field smeared against
the time-reflected test function (this is the $\varphi$ from the dictionary: a Gaussian
random variable indexed by $\theta f_j$).

**The idea (mathematics).** Two genuine ideas, stacked:
1. **A mixed representation.** The naive move — write $\langle \theta f, C f\rangle$ in
   momentum space and stare — *fails*, because the time-momentum integrand
   $1/\sqrt{\lvert k\rvert^2 + m^2}$ is not absolutely integrable. The fix is to Fourier
   transform *only the spatial* directions and keep time in position space, via a
   proper-time (Schwinger) integral. The time kernel then becomes a **pure exponential**
   $e^{-\omega_k \lvert s - t\rvert}/(2\omega_k)$, $\omega_k = \sqrt{\lvert \bar k\rvert^2 +
   m^2}$. For positive times $s, t > 0$ this factorizes,
   $e^{-\omega_k(s+t)} = e^{-\omega_k s}\,e^{-\omega_k t}$, turning $\langle \theta f, C
   f\rangle$ into a manifest sum of squared moduli $\ge 0$ — reflection positivity *of the
   covariance*.
2. **The Schur–Hadamard lift.** Positivity of the scalar $\langle \theta f, C f\rangle$
   must be promoted to positive-semidefiniteness of the whole matrix (RP). Because the
   field is Gaussian, $(\star)$ gives $M_{jk} = \rho_j \rho_k\, e^{R_{jk}}$ with $R_{jk} =
   \langle \theta f_j, C f_k\rangle$ positive semidefinite; and the **entrywise
   exponential of a PSD matrix is PSD** ($e^{R} = \sum_n R^{\odot n}/n!$, each Hadamard
   power $R^{\odot n}$ PSD by the Schur product theorem). That is real positivity theory,
   not bookkeeping.

Headline `gaussianFreeField_OS3`
([`OS3_ReflectionPositivity.lean:989`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L989)).

> **One line:** expose a factorizing exponential by a mixed representation, then lift
> scalar positivity to matrix positivity by Schur–Hadamard. Deep *and* long — full
> walkthrough in [OS3.md](OS3.md).

---

## OS4 — Clustering & ergodicity

**Second-heaviest: $\approx 2300$ lines across three files.**

**What it says (physics).** Distant regions decorrelate. **Clustering:** as two
observables are pulled apart, the expectation of their product factorizes into the product
of expectations — the statement that there is a mass gap and no long-range order.
**Ergodicity:** time averages of observables converge (in $L^2(\mu)$) to their ensemble
mean — equivalently, the vacuum is unique and $\mu$ is an extremal (pure) state.

**The idea (mathematics).** One elegant observation carries clustering, and a standard —
if lengthy — quantitative argument carries ergodicity:
- **Clustering** rests on the Gaussian **joint moment-generating factorization**
  $\mathbb{E}\big[e^{\varphi(f)+\varphi(g)}\big] = \mathbb{E}\big[e^{\varphi(f)}\big]\,
  \mathbb{E}\big[e^{\varphi(g)}\big]\, e^{\,C(f,g)}$: *all* dependence between two
  observables is squeezed into the single scalar $e^{C(f,g)}$. So the connected part is
  $\lesssim \lvert C(f, T_s g)\rvert$, and since the massive covariance decays
  *exponentially* — $\lvert C(z)\rvert \le C_0\,e^{-(m/2)\lVert z\rVert}$, the mass gap —
  clustering holds at **any** polynomial rate.
- **Ergodicity** is a quantitative $L^2$ (von Neumann–type) ergodic theorem. Stationarity
  and Fubini turn the variance of a time average into a double integral of covariances;
  polynomial clustering at rate $\alpha = 6$ bounds the integrand by $(1 + \lvert s -
  u\rvert)^{-3}$; integrability ($3 > 1$) makes the double integral $O(T)$, so the
  variance is $O(1/T) \to 0$. The ideas are standard; the length is the price of doing
  the estimate rigorously.

Headlines `gaussianFreeField_satisfies_OS4`
([`OS4_Clustering.lean:440`](../../OSforGFF/OS/OS4_Clustering.lean#L440)) and
`OS4_PolynomialClustering_implies_OS4_Ergodicity`
([`OS4_Ergodicity.lean:1301`](../../OSforGFF/OS/OS4_Ergodicity.lean#L1301)).

> **One line:** one beautiful idea (all correlation lives in $e^{C(f,g)}$; the mass gap
> kills it) plus a long, routine quantitative ergodic theorem. Full walkthrough in
> [OS4.md](OS4.md).

---

## OS0 — Analyticity

**A single file, $\approx 700$ lines — but a one-line idea wrapped in heavy plumbing.**

**What it says (physics).** The generating functional $z \mapsto Z[\sum_i z_i J_i]$ is
entire on $\mathbb{C}^n$. This is what guarantees that *all* Schwinger (correlation)
functions exist — they are the $z$-derivatives of $Z$ at the origin — and that $Z$ is
ready for analytic continuation to Minkowski time.

**The idea (mathematics).** *Trivial.* By $(\star)$, $Z[\sum_i z_i J_i] =
\exp(-\tfrac12\,Q(z))$ with $Q$ a quadratic polynomial in $z$ — and the exponential of a
polynomial is entire. Full stop. Everything else in the 700 lines is **analytic
plumbing**: promoting the real characteristic functional to complex arguments (identity
theorem), and — the bulk — justifying **differentiation under the integral sign** (the
Leibniz rule), which needs a $\mu$-integrable dominating function. That dominator is
where the one nontrivial *input* enters: **Fernique's theorem** (Gaussian measures have
exponential-square tails) plus Young's inequality. The mathematics is one algebraic
observation; the length is measure theory done honestly.

Headline `gaussianFreeField_satisfies_OS0`
([`OS0_Analyticity.lean:659`](../../OSforGFF/OS/OS0_Analyticity.lean#L659)).

> **One line:** "exp of a quadratic is entire" — the rest is the rigor of differentiating
> a functional integral. Full walkthrough in [OS0.md](OS0.md).

---

## OS1 — Regularity

**One of the two light axioms, $\approx 460$ lines, one clean estimate.** OS1 is a
temperedness bound, $\lvert Z[f]\rvert \le \exp\!\big(c\,(\lVert f\rVert_{L^1} + \lVert
f\rVert_{L^p}^p)\big)$ for some $p \in [1,2]$ (so the reconstructed correlation functions
are distributions of finite order). From $(\star)$, $\lvert Z[f]\rvert = \exp(-\tfrac12
\,\mathrm{Re}\langle f, C f\rangle)$; drop the sign, apply **Plancherel** to reach
momentum space, and cap the multiplier by the mass gap, $\widehat{C}(k) = 1/(\lvert
k\rvert^2 + m^2) \le 1/m^2$. Out drops the clean witness $p = 2$, $c = 1/(2m^2)$.

Headline `gaussianFreeField_satisfies_OS1`
([`OS1_Regularity.lean:404`](../../OSforGFF/OS/OS1_Regularity.lean#L404)).

> **One line:** $C$ is the multiplier $1/(\lvert k\rvert^2 + m^2)$, bounded by $1/m^2$ —
> that *is* the bound. Full walkthrough (with OS2) in [OS1OS2.md](OS1OS2.md).

---

## OS2 — Euclidean invariance

**The lightest axiom, $\approx 160$ lines, one symmetry.** $Z$ must be invariant under the
Euclidean group $E(d) = \mathbb{R}^d \rtimes O(d)$. A general Gaussian lemma reduces this,
once and for all, to invariance of the covariance form; and *that* is a line of geometry:
the propagator $C(x, y)$ depends only on $\lVert x - y\rVert$ (its symbol $1/(\lvert
k\rvert^2 + m^2)$ is radial), and isometries preserve distance, so $C(gx, gy) = C(x, y)$.

Supplied by `gaussian_satisfies_OS2`
([`GaussianFreeField.lean:62`](../../OSforGFF/Measure/GaussianFreeField.lean#L62)) fed by
`CovarianceEuclideanInvariantℂ_μ_GFF`
([`OS2_Invariance.lean:152`](../../OSforGFF/OS/OS2_Invariance.lean#L152)).

> **One line:** the propagator is a function of $\lVert x - y\rVert$; isometries preserve
> $\lVert x - y\rVert$. Full walkthrough (with OS1) in [OS1OS2.md](OS1OS2.md).

---

## Length is not depth: what is hard mathematics, and what is hard bookkeeping

If you are here for the *mathematics*, do not read the axioms in the order above. Proof
size measures how much measure-theoretic and analytic bookkeeping the formalization must
carry — not how deep the idea is. The two orderings disagree sharply, and the disagreement
is the most useful thing to know before you dive in.

| Axiom | Lines | Genuine mathematical idea? | Where the difficulty really lives |
|---|---|---|---|
| **OS3** | $\approx 6750$ | **Yes — the deep one.** Mixed (proper-time) representation; entrywise-exponential positivity (Schur–Hadamard); it *is* the Osterwalder–Schrader reconstruction positivity. | Split between real ideas (`MixedRep`, `CovarianceRP`, `ReflectionPositivity`) and a large, technical Fubini/integrability layer (`MixedRepInfra`, $\approx 3620$ lines). |
| **OS4 (clustering)** | part of $2300$ | **Yes — one elegant idea.** All correlation collapses into $e^{C(f,g)}$; the mass gap forces exponential decay. | Short and conceptual once you have the Gaussian MGF factorization. |
| **OS4 (ergodicity)** | part of $2300$ | **Moderate — a standard template.** A quantitative $L^2$ ergodic theorem; no new idea, but the rigorous variance/decay estimate is long. | The length is the estimate, not the concept. |
| **OS1** | $\approx 460$ | **Light — one estimate.** Plancherel + a multiplier bound. | Elementary given the mass gap. |
| **OS2** | $\approx 160$ | **Light — one symmetry.** Radial covariance + isometry invariance. | Essentially a one-liner plus a Gaussian reduction lemma. |
| **OS0** | $\approx 700$ | **None — the idea is trivial.** "$\exp$ of a quadratic is entire." | *All* of the length is analytic plumbing: differentiation under the integral, Fernique domination. The poster child for length $\ne$ depth. |

**Reading recommendation.** For mathematical substance, read **OS3** (both the analytic
maneuver and the positivity theory) and the **clustering** half of **OS4**. **OS1** and
**OS2** are elegant one-liners worth ten minutes each. **OS0** is worth reading only if you
specifically want to see how one differentiates a Gaussian functional integral rigorously —
its physics content is exhausted by "$\exp$ of a quadratic is entire."

---

## Every axiom is a property of the covariance $C$

The unifying lesson. Because the field is Gaussian, $(\star)$ collapses every OS axiom into
one property of the *single* object $C = (-\Delta + m^2)^{-1}$:

| Axiom | Property of $C$ | Mechanism | Idea vs. length |
|---|---|---|---|
| **OS2** Invariance | $C$ is **symmetric** (Euclidean) | propagator sees only $\lVert x - y\rVert$ | light idea, short |
| **OS1** Regularity | $C$ is **bounded** | Plancherel + $\widehat{C} \le 1/m^2$ | light idea, short |
| **OS0** Analyticity | $C$ is a **bilinear form** | $\exp$ of a quadratic is entire | trivial idea, *long* |
| **OS4** Clustering/ergodicity | $C$ **decays** | mass gap ⇒ exponential decay | one real idea + long estimate |
| **OS3** Reflection positivity | reflected $C$ is **positive** | mixed representation + Schur–Hadamard | deep idea, *long* |

Read top to bottom: $C$ is a bounded, symmetric, reflection-positive, decaying bilinear
form. The whole theory says the free propagator $1/(\lvert k\rvert^2 + m^2)$ has these five
properties — and, through the mass $m > 0$, they *all* trace back to that one denominator.

---

## No upper bound on the dimension

Every OS axiom — together with the Minlos construction, Plancherel, positive-definiteness,
and the covariance's decay and integrability — is **uniform in $d \ge 2$**. The lower
bound $2 \le d$ is intrinsic and permanent: reflection positivity reflects a time
coordinate, which needs a time axis and the $\mathbb{R} \times \mathbb{R}^{d-1}$ split.

The delicate point is the proper-time / spatial-momentum **Fubini exchange** inside the
OS3 mixed representation (`OS3_MixedRepInfra.integrable_dominate_G`). Positive-time
Schwartz functions are flat to *all* orders at the time boundary, and the domination uses
vanishing to order $d$: the outer proper-time integrand behaves like
$$\sim s^{(d+2)/2}\, e^{-s m^2},$$
integrable at $s = 0$ in every dimension. (First-order vanishing gives the sharp historical
constraint $d \le 5$; the history of that bound and its removal is written up in
[`../general_dimension.md`](../general_dimension.md), and the architecture in
[`../dimension_generic.md`](../dimension_generic.md).)

> **One line:** $2 \le d$ is structural and permanent; there is no upper bound — the OS3
> Fubini dominator uses order-$d$ boundary vanishing.

---

## Where to go next

**Detailed companions** (this folder): [OS3.md](OS3.md) — reflection positivity, the
Schur–Hadamard argument, and OS reconstruction; [OS4.md](OS4.md) — clustering and the
quantitative ergodic theorem; [OS0.md](OS0.md) — analyticity and differentiation under the
integral; [OS1OS2.md](OS1OS2.md) — the two light axioms and the "property of $C$" picture.

**Technical per-file summaries** (declaration-by-declaration, for when you open the Lean):
[`Master.md`](../../summary/OSforGFF/OS/Master.md),
[`Axioms.md`](../../summary/OSforGFF/OS/Axioms.md),
[`OS0_Analyticity.md`](../../summary/OSforGFF/OS/OS0_Analyticity.md),
[`OS1_Regularity.md`](../../summary/OSforGFF/OS/OS1_Regularity.md),
[`OS2_Invariance.md`](../../summary/OSforGFF/OS/OS2_Invariance.md),
[`OS3_MixedRepInfra.md`](../../summary/OSforGFF/OS/OS3_MixedRepInfra.md),
[`OS3_MixedRep.md`](../../summary/OSforGFF/OS/OS3_MixedRep.md),
[`OS3_CovarianceRP.md`](../../summary/OSforGFF/OS/OS3_CovarianceRP.md),
[`OS3_ReflectionPositivity.md`](../../summary/OSforGFF/OS/OS3_ReflectionPositivity.md),
[`OS4_MGF.md`](../../summary/OSforGFF/OS/OS4_MGF.md),
[`OS4_Clustering.md`](../../summary/OSforGFF/OS/OS4_Clustering.md),
[`OS4_Ergodicity.md`](../../summary/OSforGFF/OS/OS4_Ergodicity.md).

**Architecture** (sibling folder): [`../architecture.md`](../architecture.md) for how the
library is layered, and
[`../definitions_entering_OS_axioms.md`](../definitions_entering_OS_axioms.md) for the
precise definitions entering the axiom statements.
