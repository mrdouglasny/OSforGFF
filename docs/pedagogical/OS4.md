# OS4 — Clustering & Ergodicity: the mass gap, decorrelation, and a unique vacuum

*A pedagogical companion for a reader who knows Euclidean QFT and functional
integrals but not Lean. The physics and the mathematical ideas lead; the Lean
names in `monospace` are just clickable anchors into the formalization, and you
can ignore them. (I say this once: throughout, every `Foo.lean:NNN` link points at
the exact declaration that carries the claim — open them only if you want to see
the proof, never to follow the argument.) OS4 is the second-heaviest axiom by
proof size — about $2300$ lines across three files — but, as we'll see, that length
is mostly a rigorous estimate wrapped around a single beautiful idea.*

---

## The objects, in one breath

Everything below is about a handful of objects; if you have read
[Overview.md](Overview.md) you know them already.

- **Field configuration** $\omega$ — a random tempered distribution, the "field."
- **Smeared field** $\varphi(f) := \langle \omega, f\rangle$ — the field tested
  against a Schwartz function $f$. For fixed $f$ this is a **random variable** on
  the probability space $(\mathscr{S}', \mu)$; that is the meaning of $\varphi$
  everywhere here.
- **The measure** $\mu$ — the mean-zero Gaussian probability measure on field
  configurations with covariance $C$.
- **Covariance / propagator** $C = (-\Delta + m^2)^{-1}$ — the two-point function
  $\mathbb{E}[\varphi(f)\,\varphi(g)] = \langle f, C g\rangle$, momentum symbol
  $\widehat{C}(k) = 1/(\lvert k\rvert^2 + m^2)$. The mass $m > 0$ is the whole
  story of OS4: it is what makes $C$ decay **exponentially** in position space.
- **Time translation** $T_s$ — the shift of a field configuration by $s$ along the
  time axis, $x = (x_0, \bar x) \mapsto (x_0 + s, \bar x)$. Because $\mu$ is
  built from a translation-invariant $C$, it is $T_s$-invariant: the field is
  **stationary** in time.

---

## 0. What OS4 asks for (physics)

**What it says.** OS4 is the precise statement that *distant regions of the field
decorrelate*. It has two faces.

- **Clustering.** Pull two observables far apart and the expectation of their
  product factorizes into the product of expectations,
  $\mathbb{E}[A\,B] \to \mathbb{E}[A]\,\mathbb{E}[B]$. Physically: there is a **mass
  gap** and no long-range order — the connected correlation function dies as the
  separation grows. For a *time* separation $s$ the library asks this at a
  **quantitative (polynomial) rate**.
- **Ergodicity.** Time averages of an observable converge, in $L^2(\mu)$, to its
  ensemble average. Writing $A(\omega) = \sum_j z_j\, e^{\varphi(f_j)}$ for a finite
  combination of exponential observables,
  $$\lim_{T\to\infty}\ \Big\lVert\ \tfrac1T\!\int_0^T A(T_s\omega)\,ds\ -\
  \mathbb{E}_\mu[A]\ \Big\rVert_{L^2(\mu)}^2 \;=\;0. \tag{ERG}$$
  This is the Glimm–Jaffe formulation; the Lean predicate is `OS4_Ergodicity`
  ([`OS/Axioms.lean:158`](../../OSforGFF/OS/Axioms.lean#L158)), and clustering is
  `OS4_Clustering` ([`OS/Axioms.lean:145`](../../OSforGFF/OS/Axioms.lean#L145)).

For a **stationary** measure these are two sides of one coin: decorrelation in time
is exactly what forces a long time average to lose memory of its starting
configuration and collapse onto the mean. OS4 makes that precise and quantitative,
and — through the reconstruction OS3 sets up — it is the statement that the physical
theory has a **single, pure vacuum** (see §5).

> **One line:** the mass gap $m > 0$ makes correlations decay exponentially; every
> quantitative claim in OS4 is a consequence of that one fact.

---

## 1. The shape of the argument — and where the real mathematics is

OS4 is a small Gaussian base plus two pieces: clustering, and ergodicity *derived
from* clustering.

```
  OS4_MGF.lean                     shared Gaussian input
    │   𝔼[e^{φ(f)}] = exp(½ S₂(f,f))            the moment-generating functional
    │   𝔼[e^{φ(f)+φ(g)}] = E_f · E_g · e^{S₂(f,g)}   Gaussian factorization
    ├──────────────────────────────┐
    ▼                              ▼
  OS4_Clustering.lean          OS4_Ergodicity.lean
    clustering, any rate α  ──▶  polynomial clustering (α = 6)
                                   ⟹  L² ergodic theorem
    │                              │
    ▼                              ▼
  os4_clustering                 os4_ergodicity        (fields of SatisfiesAllOS)
```

**This is the one thing to take away before reading further.** The two halves of
OS4 are utterly different in mathematical character, and the difference is worth
more than any proof detail:

- **Clustering rests on ONE elegant idea.** Because the field is Gaussian, *all* the
  correlation between two observables collapses into a single scalar factor
  $e^{S_2(f,g)}$, where $S_2(f,g) = \langle f, C g\rangle$ is the cross-covariance.
  Control that one number and you control everything — and the mass gap makes it
  decay exponentially. Conceptually, clustering is a paragraph, not a program.
- **Ergodicity is a standard template.** It is a quantitative $L^2$ (von Neumann /
  Cesàro-type) ergodic theorem: bound the variance of a time average and show it
  vanishes. There is **no new idea** here — the argument is the textbook one — but
  doing the variance estimate rigorously is long. *The length is the estimate, not
  a concept.* Do not mistake its line count for depth.

Everything below unpacks these. Section 2 is the Gaussian input; §3 is clustering
(the idea); §4 is the ergodic theorem (the estimate); §5 is the physics; §6 the
dimension note; §7 sorts the two halves by genuine difficulty.

---

## 2. The Gaussian foundation (`OS4_MGF`)

**The idea.** Everything rests on the **moment-generating functional** of the
Gaussian measure. For a single (complex) test function $J$,
$$\mathbb{E}_\mu\!\left[e^{\varphi(J)}\right] \;=\;
\exp\!\left(\tfrac12\, S_2(J,J)\right), \qquad
S_2(J,J) = \langle J, C J\rangle,\ \ C = (-\Delta+m^2)^{-1}. \tag{MGF}$$
This is the same Gaussian identity as the characteristic functional
$Z[J] = \mathbb{E}[e^{i\varphi(J)}] = \exp(-\tfrac12\langle J, C J\rangle)$ of the
[Overview](Overview.md), with $i$ replaced by $1$ (hence the sign flip on the
$\tfrac12$). In Lean it is
`gff_mgf_formula` ([`OS/OS4_MGF.lean:178`](../../OSforGFF/OS/OS4_MGF.lean#L178)).

The **real workhorse** is the *joint* version — the whole reason OS4 is tractable:
$$\mathbb{E}_\mu\!\left[e^{\varphi(f)+\varphi(g)}\right] \;=\;
\mathbb{E}_\mu\!\left[e^{\varphi(f)}\right]\,
\mathbb{E}_\mu\!\left[e^{\varphi(g)}\right]\, e^{\,S_2(f,g)}, \qquad
S_2(f,g) = \langle f, C g\rangle. \tag{JOINT}$$
Read it slowly. The product of the two single expectations is the **fully
decorrelated** answer — what you would get if $\varphi(f)$ and $\varphi(g)$ were
independent. The *entire* remaining dependence between the two observables is
squeezed into the single scalar factor $e^{\,S_2(f,g)}$. This is special to
Gaussians, and it is the pivot of the whole axiom: **to control correlations,
control the one number $S_2(f,g)$.** In Lean,
`gff_joint_mgf_factorization` ([`OS/OS4_MGF.lean:222`](../../OSforGFF/OS/OS4_MGF.lean#L222)).

Two small auxiliary lemmas earn their place:

- **Time-translation duality**
  ([`OS/OS4_MGF.lean:99`](../../OSforGFF/OS/OS4_MGF.lean#L99)):
  $\langle T_s\omega, g\rangle = \langle\omega, T_{-s}g\rangle$. This moves a time
  shift off the *rough* field configuration $\omega$ and onto the *smooth* test
  function $g$, where the covariance kernel can act on it. Combined with translation
  invariance of $C$, it makes the MGF **time-invariant**
  ([`OS/OS4_MGF.lean:209`](../../OSforGFF/OS/OS4_MGF.lean#L209)),
  $\mathbb{E}_\mu[e^{\varphi(T_s f)}] = \mathbb{E}_\mu[e^{\varphi(f)}]$ — this is the
  stationarity that ergodicity will lean on.
- **The linearization bound**
  ([`OS/OS4_MGF.lean:254`](../../OSforGFF/OS/OS4_MGF.lean#L254)):
  $\lVert e^x - 1\rVert \le \lVert x\rVert\, e^{\lVert x\rVert}$ for complex $x$.
  This turns "the factor $e^{\,S_2}$ is close to $1$" into a bound proportional to
  $\lvert S_2\rvert$ — the bridge from (JOINT) to a decay estimate.

> **One line:** the joint factorization $e^{\,S_2(f,g)}$ is the hinge; the two
> helpers move the time shift onto the kernel and linearize the exponential.

---

## 3. Clustering — the one elegant idea (`OS4_Clustering`)

**What it says.** Two observables built from far-separated test functions
decorrelate. The library proves this in two forms: a **qualitative** version at
large *spatial* separation $a$,
$$\big\lVert\ Z[f + T_a g] - Z[f]\,Z[g]\ \big\rVert < \varepsilon
\qquad \text{for } \lVert a\rVert > R(\varepsilon), \tag{C}$$
(`gaussianFreeField_satisfies_OS4`,
[`OS/OS4_Clustering.lean:440`](../../OSforGFF/OS/OS4_Clustering.lean#L440)), and a
**quantitative** version at a polynomial rate in *time* separation $s$: for every
$f,g$ there is a constant $c = c(f,g)$ with
$$\left\lvert\ \mathbb{E}_\mu\!\left[e^{\varphi(f)+\langle T_s\omega,\,g\rangle}\right]
- \mathbb{E}_\mu\!\left[e^{\varphi(f)}\right]
  \mathbb{E}_\mu\!\left[e^{\varphi(g)}\right]\ \right\rvert
\;\le\; c\,(1+s)^{-\alpha}, \qquad s\ge0, \tag{PC}$$
for **any** exponent $\alpha > 0$ (`gaussianFreeField_satisfies_OS4_PolynomialClustering`,
[`OS/OS4_Clustering.lean:576`](../../OSforGFF/OS/OS4_Clustering.lean#L576)). The
polynomial form is the one ergodicity consumes; the qualitative form is what the
master theorem installs into `os4_clustering`.

**The idea — three moves, and only the third is analysis.** Apply (JOINT), after
using time duality to move the shift onto $g$ (write $g_s := T_{-s}g$):

1. **Factorize.** The correlation minus its decorrelated value is exactly
   $\big\lvert E_f\,E_g\big\rvert\cdot\big\lvert e^{\,S_2(f, g_s)}-1\big\rvert$.
   All the separation dependence sits in that lone factor $e^{\,S_2(f,g_s)}$ — this
   is (JOINT) doing all the conceptual work.
2. **Linearize.** By the bound $\lvert e^{S_2}-1\rvert \le \lvert S_2\rvert\,
   e^{\lvert S_2\rvert}$, the gap is $\lesssim \lvert S_2(f, g_s)\rvert$. So the
   whole question reduces to: *how fast does the cross-covariance $S_2(f, g_s)$
   decay as the shift $s$ grows?*
3. **Kernel decay.** Writing $S_2(f, g_s)$ as the convolution integral
   $\iint f(x)\,K(x-y)\,g(y - s\hat e_0)\,dy\,dx$ against the covariance kernel
   $K$ ([`OS/OS4_Clustering.lean:554`](../../OSforGFF/OS/OS4_Clustering.lean#L554)),
   the answer is dictated entirely by the decay of $K$.

**Why every polynomial rate is free.** The massive kernel decays *exponentially* —
this is the mass gap made quantitative:
$$\lvert K(z)\rvert \;\le\; A\, e^{-(m/2)\,\lVert z\rVert}, \qquad \lVert z\rVert \ge 1
\tag{GAP}$$
(`freeCovarianceKernel_exp_decay`,
[`Covariance/ParsevalGeneric.lean:1058`](../../OSforGFF/Covariance/ParsevalGeneric.lean#L1058)).
Since exponential decay beats every polynomial, $S_2(f, g_s)$ decays faster than
$(1+s)^{-\alpha}$ for *any* $\alpha > 0$ — which is why (PC) can be stated for an
arbitrary $\alpha$. This freedom to name the rate is precisely what ergodicity
exploits next.

That is the entire mathematics of clustering. It is one observation — (JOINT) puts
all correlation in $e^{S_2}$ — married to one fact — (GAP), the mass gap. No
estimate is deep; the file's length is convolution and Schwartz-decay bookkeeping,
not ideas.

> **One line:** all correlation lives in $e^{S_2(f,g)}$; the mass gap kills $S_2$
> exponentially; so clustering holds at every polynomial rate for free.

---

## 4. Ergodicity — a standard quantitative $L^2$ theorem (`OS4_Ergodicity`)

**What it says.** The time average of an observable converges to its mean in
$L^2(\mu)$ — equation (ERG). This is genuine mathematics and genuinely rigorous, but
it is a **standard template**: the classical von Neumann / Cesàro ergodic argument,
made quantitative. *There is no new idea here.* What follows is long because the
variance estimate is done honestly, not because anything is subtle. Read it once to
see the template; do not expect a surprise.

**The strategy.** Fix a single exponential generator
$A_s(\omega) = e^{\langle T_s\omega, f\rangle}$ with mean
$E_A = \mathbb{E}_\mu[A_0]$. Ergodicity-for-generators
([`OS/OS4_Ergodicity.lean:83`](../../OSforGFF/OS/OS4_Ergodicity.lean#L83)) is the
statement that the **variance of the time average vanishes**,
$$\mathrm{Var}_T \;:=\; \mathbb{E}_\mu\!\left[\Big\lVert\tfrac1T\!\int_0^T A_s\,ds
- E_A\Big\rVert^2\right]\ \xrightarrow[T\to\infty]{}\ 0,$$
and the full axiom (ERG) over all finite combinations $\sum_j z_j A^{(j)}$ follows
from this single-generator case (§4.4). The driver is polynomial clustering at the
generous rate $\alpha = 6$ (`OS4''_Clustering`,
[`OS/OS4_Ergodicity.lean:96`](../../OSforGFF/OS/OS4_Ergodicity.lean#L96)), packaged
as the master implication
`OS4_PolynomialClustering_implies_OS4_Ergodicity`
([`OS/OS4_Ergodicity.lean:1301`](../../OSforGFF/OS/OS4_Ergodicity.lean#L1301)) that
the assembly feeds into `os4_ergodicity`. Four steps:

**Step 1 — variance is a double integral of covariances.** Expand the squared norm
and use Fubini
([`OS/OS4_Ergodicity.lean:583`](../../OSforGFF/OS/OS4_Ergodicity.lean#L583)):
$$\mathrm{Var}_T \;\le\; \frac{1}{T^2}\int_0^T\!\!\int_0^T
\big\lVert\,\mathrm{Cov}(s,u)\,\big\rVert\,ds\,du, \qquad
\mathrm{Cov}(s,u) = \mathbb{E}_\mu\!\left[A_s\,\overline{A_u}\right]
- E_A\,\overline{E_A}. \tag{VAR}$$
This is clean because the field is **stationary**: $\lVert A_s\rVert_{L^2}$ is
independent of $s$ ([`OS/OS4_Ergodicity.lean:222`](../../OSforGFF/OS/OS4_Ergodicity.lean#L222),
the OS2 time-invariance input), and $\mathrm{Cov}(s,u)$ depends only on $s-u$
([`OS/OS4_Ergodicity.lean:379`](../../OSforGFF/OS/OS4_Ergodicity.lean#L379)) and is
jointly continuous
([`OS/OS4_Ergodicity.lean:503`](../../OSforGFF/OS/OS4_Ergodicity.lean#L503)).

**Step 2 — clustering gives covariance decay.** The covariance $\mathrm{Cov}(s,u)$
*is* the clustering gap (PC) at separation $\lvert s-u\rvert$ (up to conjugation).
So polynomial clustering at $\alpha = 6$ yields
([`OS/OS4_Ergodicity.lean:727`](../../OSforGFF/OS/OS4_Ergodicity.lean#L727))
$$\big\lVert\,\mathrm{Cov}(s,u)\,\big\rVert \;\le\; c\,(1+\lvert s-u\rvert)^{-3}.
\tag{COV}$$
(The exponent drops from $6$ to $3$ by a one-line monotonicity step; any exponent
$>1$ would do — see the subtlety below.)

**Step 3 — the double integral grows only linearly.** With an integrable decay
exponent, the integral over the square is $O(T)$, not $O(T^2)$
([`OS/OS4_Ergodicity.lean:366`](../../OSforGFF/OS/OS4_Ergodicity.lean#L366)):
$$\int_0^T\!\!\int_0^T (1+\lvert s-u\rvert)^{-3}\,ds\,du \;\le\; 2\,T\,C. \tag{DI}$$
The mechanism is elementary: fix $s$; the inner integral is bounded by the
convergent tail $\int_{\mathbb{R}}(1+\lvert r\rvert)^{-3}\,dr < \infty$ — finite
**precisely because the exponent $3 > 1$** — and integrating that bounded value over
$s \in [0,T]$ contributes the single factor $T$.

**Step 4 — assemble.** Chain (VAR) → (COV) → (DI)
([`OS/OS4_Ergodicity.lean:895`](../../OSforGFF/OS/OS4_Ergodicity.lean#L895)):
$$\mathrm{Var}_T \;\le\; \frac{1}{T^2}\cdot c\cdot 2TC \;=\; \frac{2cC}{T}\
\xrightarrow[T\to\infty]{}\ 0.$$
The familiar ergodic $1/T$ fluctuation, here a clean consequence of **summable
correlations**.

**The $\alpha = 6$ is generous, not sharp.** Nothing forces $6$. The only genuine
requirement is that, after the reduction, the time-integral exponent exceed $1$ so
that (DI) converges — i.e. covariance decay faster than $(1+\lvert s-u\rvert)^{-1}$.
The proof reduces $-6$ to $-3$ for convenience, and *any* $\alpha > 1$ would work;
recall (§3) that the massive field supplies clustering at **every** $\alpha > 0$ for
free, so $6$ is just a round, safely-large pick. (A source comment records a
dimensional heuristic $\alpha = 2d$; the operative fact is only "$>1$ after
reduction.")

### 4.4 From generators to all observables

A general observable is a finite combination $A = \sum_j z_j A^{(j)}$. Its
time-average error is the sum of the per-term errors, and Cauchy–Schwarz in the
finite index $j$ bounds the $L^2$ norm of the sum by the per-term norms, each
$\to 0$ by Step 4 ([`OS/OS4_Ergodicity.lean:1077`](../../OSforGFF/OS/OS4_Ergodicity.lean#L1077),
using the elementary
[`OS/OS4_Ergodicity.lean:1061`](../../OSforGFF/OS/OS4_Ergodicity.lean#L1061)). Hence
(ERG) holds for every finite combination — the full `OS4_Ergodicity`.

> **One line:** variance $=$ double integral of covariances; clustering makes the
> integrand summable; so the average of the square is $O(1/T) \to 0$, and
> Cauchy–Schwarz lifts single exponentials to all observables. A textbook ergodic
> theorem — its size is the rigor, not the idea.

---

## 5. Why ergodicity matters — a unique, pure vacuum

Clustering and ergodicity are the statements that the reconstructed quantum theory
has a **single physical vacuum**. In the Osterwalder–Schrader / Glimm–Jaffe picture,
OS3 reconstructs a physical Hilbert space $\mathcal{H}_{\mathrm{phys}}$, a
positive Hamiltonian $H \ge 0$, and a vacuum $\Omega$; OS4 then pins down that the
vacuum is unique and pure.

- **Clustering $\Leftrightarrow$ the vacuum is unique.** Factorization of
  long-separation correlations,
  $\langle\Omega, A\, e^{-\lvert s\rvert H} B\,\Omega\rangle \to
  \langle\Omega, A\,\Omega\rangle\langle\Omega, B\,\Omega\rangle$, says no second
  translation-invariant state is mixed in — equivalently the energy-$0$ eigenspace
  of $H$ is one-dimensional, a **mass gap above the vacuum**. A theory that failed
  to cluster would be a nontrivial mixture of pure phases.
- **Ergodicity $\Leftrightarrow$ extremality of the measure.** Equation (ERG) — time
  averages converging to the mean — is exactly the statement that $\mu$ is an
  **extremal** (ergodic) translation-invariant measure: it cannot be written as a
  nontrivial convex combination of invariant measures. That is the probabilistic
  face of "unique vacuum."

So OS4 is the axiom that selects a single physical vacuum, and for the GFF its truth
traces back to one analytic fact: the **mass gap $m > 0$ makes correlations decay
exponentially**. Massless ($m=0$) fields cluster only marginally and the story is
genuinely different — one more reason the library insists on $m > 0$.

---

## 6. Dimension note — the mechanism is uniform in $d \ge 2$

Unlike OS3, whose spatial integrability estimate is genuinely dimension-specific,
the **OS4 mechanism is dimension-agnostic**. Everything above depends on the
propagator only through the single exponential rate (GAP), and that bound is
supplied *uniformly in $d$* by the `GFFPropagator d m` interface (its `decayBound`
field), which reads it off the **proper-time (Schwinger) representation** of the
massive covariance — a representation that exists in every dimension.

The large-separation asymptotics of the kernel *do* carry dimension-specific
prefactors — an $e^{-mr}/r^{(d-2)/2}$-type dressing of a Bessel profile ($K_0$ for
$d = 2$, the $K_{1/2}$ Yukawa for $d = 3$, $K_1$ for $d = 4$, $K_{3/2}$ for
$d = 5$) — but **only the exponential factor matters for OS4**: it is what makes
clustering hold at any polynomial rate (§3) and what makes the time-averaged
variance summable (§4). Every lemma above runs over the section variables
`{d : ℕ} [Fact (2 ≤ d)]`; the proof is written once and instantiates unchanged in
every dimension $d \ge 2$. (The lower bound $d \ge 2$ is only there so a time axis
exists to translate along; no OS axiom imposes an upper bound on the dimension.)

---

## 7. Length is not depth

The two halves of OS4 are worth ranking by genuine mathematical content, because
their line counts mislead in opposite directions.

| Half | Genuine idea? | Where the difficulty lives |
|---|---|---|
| **Clustering** | **Yes — one elegant idea.** All correlation collapses into $e^{S_2(f,g)}$; the mass gap (GAP) forces exponential decay. | Short and conceptual once you have the Gaussian factorization (JOINT). The file's bulk is convolution/Schwartz-decay bookkeeping. |
| **Ergodicity** | **No new idea — a standard template.** A quantitative $L^2$ ergodic theorem (variance $\to 0$). Real and rigorous, but the argument is textbook. | *The length is the estimate, not the concept*: Fubini, stationarity, the integrable-tail bound (DI), and the squeeze. |

**Reading recommendation.** For mathematical substance, read §3 (clustering) closely
and skim §4 (ergodicity) once for the template. The single fact worth carrying away
is that a massive Gaussian field decorrelates *because* its propagator decays
exponentially — and that one fact, through (JOINT), is both halves of OS4.

---

## 8. One-paragraph summary

OS4 is proved on a Gaussian base. `OS4_MGF` gives the factorization
$\mathbb{E}[e^{\varphi(f)+\varphi(g)}] =
\mathbb{E}[e^{\varphi(f)}]\,\mathbb{E}[e^{\varphi(g)}]\,e^{S_2(f,g)}$, reducing all
correlations to the single cross-covariance $S_2(f,g) = \langle f, C g\rangle$.
`OS4_Clustering` then shows correlations factorize at separation $s$ with gap
$\lesssim \lvert S_2(f, T_{-s}g)\rvert$ (linearizing via
$\lVert e^z - 1\rVert \le \lVert z\rVert e^{\lVert z\rVert}$), and since the massive
kernel decays exponentially, $\lvert K(z)\rvert \le A\,e^{-(m/2)\lVert z\rVert}$,
this holds at **any** polynomial rate — one elegant idea. `OS4_Ergodicity` then runs
a standard quantitative $L^2$ ergodic theorem: the variance of the time average is,
by Fubini and stationarity, a double integral of covariances; clustering at
$\alpha = 6$ bounds $\lVert\mathrm{Cov}(s,u)\rVert \le c(1+\lvert s-u\rvert)^{-3}$;
integrability ($3 > 1$) makes the double integral $O(T)$; so the variance is
$O(1/T) \to 0$, which is $L^2$-convergence of time averages to the mean, lifted to
all observables by Cauchy–Schwarz. Everything is uniform in the spacetime dimension
$d$.

---

## 9. Pointers into the code

| Result | Name (line) |
|---|---|
| OS4 clustering axiom (statement) | [`OS4_Clustering`](../../OSforGFF/OS/Axioms.lean#L145) — `OS/Axioms.lean:145` |
| OS4 ergodicity axiom (statement) | [`OS4_Ergodicity`](../../OSforGFF/OS/Axioms.lean#L158) — `OS/Axioms.lean:158` |
| Polynomial clustering (statement) | [`OS4_PolynomialClustering`](../../OSforGFF/OS/Axioms.lean#L180) — `OS/Axioms.lean:180` |
| Time-translation duality | [`timeTranslationDistribution_pairingℂ`](../../OSforGFF/OS/OS4_MGF.lean#L99) — `OS/OS4_MGF.lean:99` |
| Gaussian MGF formula (MGF) | [`gff_mgf_formula`](../../OSforGFF/OS/OS4_MGF.lean#L178) — `OS/OS4_MGF.lean:178` |
| MGF time-translation invariance | [`gff_generating_time_invariant`](../../OSforGFF/OS/OS4_MGF.lean#L209) — `OS/OS4_MGF.lean:209` |
| Joint MGF factorization (JOINT) | [`gff_joint_mgf_factorization`](../../OSforGFF/OS/OS4_MGF.lean#L222) — `OS/OS4_MGF.lean:222` |
| Linearization $\lVert e^x-1\rVert$ bound | [`exp_sub_one_bound_general`](../../OSforGFF/OS/OS4_MGF.lean#L254) — `OS/OS4_MGF.lean:254` |
| GFF satisfies clustering (C) | [`gaussianFreeField_satisfies_OS4`](../../OSforGFF/OS/OS4_Clustering.lean#L440) — `OS/OS4_Clustering.lean:440` |
| GFF satisfies polynomial clustering (PC) | [`gaussianFreeField_satisfies_OS4_PolynomialClustering`](../../OSforGFF/OS/OS4_Clustering.lean#L576) — `OS/OS4_Clustering.lean:576` |
| $S_2(f,T_{-s}g)$ as convolution integral | [`schwinger2_time_translated_eq_bilinear`](../../OSforGFF/OS/OS4_Clustering.lean#L554) — `OS/OS4_Clustering.lean:554` |
| Small-decay ⇒ clustering (real) | [`GFF_OS4_from_small_decay_real`](../../OSforGFF/OS/OS4_Clustering.lean#L183) — `OS/OS4_Clustering.lean:183` |
| Cross-covariance vanishes at ∞ (real) | [`schwartz_cross_covariance_decay_real`](../../OSforGFF/OS/OS4_Clustering.lean#L311) — `OS/OS4_Clustering.lean:311` |
| α=6 clustering instance | [`OS4''_Clustering`](../../OSforGFF/OS/OS4_Ergodicity.lean#L96) — `OS/OS4_Ergodicity.lean:96` |
| Generator-ergodicity Prop | [`OS4'_Ergodicity_generating`](../../OSforGFF/OS/OS4_Ergodicity.lean#L83) — `OS/OS4_Ergodicity.lean:83` |
| Stationarity of $\lVert A_s\rVert_{L^2}$ | [`gff_exp_L2_norm_constant`](../../OSforGFF/OS/OS4_Ergodicity.lean#L222) — `OS/OS4_Ergodicity.lean:222` |
| Covariance depends only on $s-u$ | [`gff_product_expectation_stationarity`](../../OSforGFF/OS/OS4_Ergodicity.lean#L379) — `OS/OS4_Ergodicity.lean:379` |
| Covariance continuity | [`gff_covariance_continuous`](../../OSforGFF/OS/OS4_Ergodicity.lean#L503) — `OS/OS4_Ergodicity.lean:503` |
| Variance ≤ double integral (VAR) | [`L2_time_average_variance_bound`](../../OSforGFF/OS/OS4_Ergodicity.lean#L583) — `OS/OS4_Ergodicity.lean:583` |
| Clustering ⇒ covariance decay (COV) | [`clustering_implies_covariance_decay`](../../OSforGFF/OS/OS4_Ergodicity.lean#L727) — `OS/OS4_Ergodicity.lean:727` |
| Double integral $O(T)$ (DI) | [`double_integral_decay_bound`](../../OSforGFF/OS/OS4_Ergodicity.lean#L366) — `OS/OS4_Ergodicity.lean:366` |
| Variance $\to 0$ | [`variance_decay_from_clustering`](../../OSforGFF/OS/OS4_Ergodicity.lean#L895) — `OS/OS4_Ergodicity.lean:895` |
| Cauchy–Schwarz in $j$ | [`norm_sq_weighted_sum_le`](../../OSforGFF/OS/OS4_Ergodicity.lean#L1061) — `OS/OS4_Ergodicity.lean:1061` |
| Generators ⇒ all observables | [`OS4'_implies_OS4`](../../OSforGFF/OS/OS4_Ergodicity.lean#L1077) — `OS/OS4_Ergodicity.lean:1077` |
| Clustering ⇒ ergodicity (master) | [`OS4_PolynomialClustering_implies_OS4_Ergodicity`](../../OSforGFF/OS/OS4_Ergodicity.lean#L1301) — `OS/OS4_Ergodicity.lean:1301` |
| Mass-gap kernel decay (GAP) | [`freeCovarianceKernel_exp_decay`](../../OSforGFF/Covariance/ParsevalGeneric.lean#L1058) — `Covariance/ParsevalGeneric.lean:1058` |

The master assembly ([`OS/Master.lean:61`](../../OSforGFF/OS/Master.lean#L61),
`gaussianFreeField_satisfies_all_OS_axioms_generic`) sets
`os4_clustering := QFT.gaussianFreeField_satisfies_OS4 m`
([`:70`](../../OSforGFF/OS/Master.lean#L70)) and `os4_ergodicity :=
OS4_Ergodicity.OS4_PolynomialClustering_implies_OS4_Ergodicity m (…​ m 6 …)`
([`:71`](../../OSforGFF/OS/Master.lean#L71)) as the two OS4 fields of
`SatisfiesAllOS (μ_GFF d m)`. Declaration-by-declaration summaries live at
[`OS4_MGF.md`](../../summary/OSforGFF/OS/OS4_MGF.md),
[`OS4_Clustering.md`](../../summary/OSforGFF/OS/OS4_Clustering.md), and
[`OS4_Ergodicity.md`](../../summary/OSforGFF/OS/OS4_Ergodicity.md).

---

*Companions: [Overview.md](Overview.md) — the map of all six axioms; [OS0.md](OS0.md)
— analyticity and differentiation under the integral; [OS1OS2.md](OS1OS2.md) —
regularity and Euclidean invariance; [OS3.md](OS3.md) — reflection positivity and
the Osterwalder–Schrader reconstruction that gives the Hilbert space, the
Hamiltonian $H \ge 0$, and the vacuum $\Omega$ whose uniqueness OS4 establishes.*
</content>
</invoke>
