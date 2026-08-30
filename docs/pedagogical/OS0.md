# OS0 — Analyticity of the Generating Functional

*A physics-first walkthrough of the analyticity axiom for the **dimension-generic**
Gaussian Free Field (every $d \ge 2$). Written for a reader who knows Euclidean QFT
and functional integrals but not Lean: the mathematics leads, and the Lean names in
`monospace` are optional clickable anchors into the formalization — ignore them on a
first read.*

OS0 is the axiom you would expect to be the hardest — "the whole correlation hierarchy
exists and is analytic" — and it is the one whose *idea* is the most trivial. That gap
is the entire point of this note. The mathematical content is a single line — **the
exponential of a quadratic polynomial is entire** — and essentially all of the
$\approx 700$-line proof is measure-theoretic *plumbing* that makes that line rigorous
as a statement about an integral. OS0 is the poster child for **length $\ne$ depth**.

> **One line:** $Z\big[\sum_i z_i J_i\big] = \exp\!\big(-\tfrac12 Q(z)\big)$ with $Q$ a
> quadratic polynomial in $z$, so it is manifestly entire. Everything else is the rigor
> of differentiating a functional integral.

---

## The objects (a 30-second dictionary)

Everything below is phrased in terms of a few objects; if some are already reflexes,
skim.

- **Field configuration** $\omega$ — a tempered distribution, $\omega \in
  \mathscr{S}'(\mathbb{R}^d)$: a "random field" you integrate against test functions,
  not a pointwise function. The set of all $\omega$ is the sample space.
- **Test function** $f$ — a Schwartz function (smooth, rapidly decaying); complex-valued
  where the $z_i$ below force it to be.
- **Smeared field** $\varphi(f) := \langle \omega, f\rangle = \omega(f)$ — the field
  tested against $f$, morally $\int \omega(x)\, f(x)\, d^d x$. For a *fixed* $f$ this is a
  **random variable** on the probability space $(\mathscr{S}', \mu)$.
- **The measure** $\mu \equiv \mu_{\mathrm{GFF}}$ — the mean-zero **Gaussian** probability
  measure on $\mathscr{S}'(\mathbb{R}^d)$ with covariance $C$; expectations $\mathbb{E}$
  are against $\mu$. In Lean it is `gaussianFreeField_free m`, aliased `μ_GFF d m`
  ([OS/Measure/Construct.lean:142](../../OSforGFF/Measure/Construct.lean#L142)).
- **Covariance / propagator** $C = (-\Delta + m^2)^{-1}$ — the two-point function,
  $\mathbb{E}\big[\varphi(f)\,\varphi(g)\big] = \langle f, C g\rangle$, with momentum-space
  symbol $\widehat{C}(k) = 1/(\lvert k\rvert^2 + m^2)$. The mass $m > 0$ is the whole
  reason everything converges.
- **Generating (characteristic) functional**
  $$Z[J] \;:=\; \mathbb{E}\big[e^{\,i\varphi(J)}\big] \;=\; \int e^{\,i\langle \omega, J\rangle}\, d\mu(\omega). \tag{GF}$$
  Because $\mu$ is Gaussian,
  $$Z[J] \;=\; \exp\!\Big(-\tfrac12\,\langle J, C J\rangle\Big). \tag{$\star$}$$
  Formula $(\star)$ is the hinge: read OS0 as "one analyticity property of $C$, seen
  through $(\star)$."

In Lean the functional (GF) is `GJGeneratingFunctionalℂ`
([OS/Spacetime/Basic.lean:241](../../OSforGFF/Spacetime/Basic.lean#L241)); the smeared
field $\langle\omega, f\rangle$ for complex $f$ is `distributionPairingℂ_real`.

---

## 1. What OS0 asks for

**What it says (physics).** Fix a finite family of complex test functions $J_1, \dots,
J_n$ and form a source $J = \sum_i z_i J_i$ with complex weights $z = (z_1, \dots, z_n)
\in \mathbb{C}^n$. OS0 demands that

$$z \;\longmapsto\; Z\!\Big[\textstyle\sum_i z_i J_i\Big]$$

be **entire** — complex-analytic on *all* of $\mathbb{C}^n$, no radius limit.

In Lean this is the predicate `OS0_Analyticity`
([OS/Axioms.lean:76](../../OSforGFF/OS/Axioms.lean#L76)); the free-field instance is the
headline theorem `gaussianFreeField_satisfies_OS0`
([OS/OS0_Analyticity.lean:659](../../OSforGFF/OS/OS0_Analyticity.lean#L659)), harvested as
the `os0` field of the bundled `SatisfiesAllOS (μ_GFF d m)`
([OS/Axioms.lean:195](../../OSforGFF/OS/Axioms.lean#L195)). The analyticity is in the
**complex parameters $z$**, with the test functions held fixed — *not* in the field
configuration $\omega$.

> **One line:** OS0 = "$z \mapsto Z[\sum_i z_i J_i]$ is entire on $\mathbb{C}^n$."

---

## 2. Why analyticity matters physically

OS0 is numbered "0" because it is the *minimal regularity* a Euclidean theory must have
before its correlation functions even make sense. Three payoffs:

**(a) All Schwinger functions exist, as derivatives at the origin.** Expanding $Z[\sum_i
z_i J_i]$ in a power series in $z$, the coefficients are exactly the **Schwinger
functions** (Euclidean $n$-point correlation functions):

$$S_n(J_1,\dots,J_n) \;=\; \frac{\partial^n}{\partial z_1 \cdots \partial z_n}\, Z\!\Big[\textstyle\sum_i z_i J_i\Big]\bigg|_{z=0}.$$

Entirety guarantees this Taylor series converges — *every* moment is finite and the whole
correlation hierarchy is recovered from $Z$ by differentiation. Without OS0 the field
might have finite second moments but divergent fourth moments, and "the $n$-point
function" would be a formal fiction.

**(b) The gateway to Minkowski space.** Euclidean QFT earns its keep because its
correlators **analytically continue** to the real-time (Wightman) functions of a
relativistic theory — the rigorous content of "Wick rotation." That continuation in the
time variables is only possible if the generating functional is analytic to begin with.
OS0 is the seed of analyticity that OS reconstruction (using OS3's positive Hamiltonian)
later extends from imaginary to real time.

**(c) Entirety is the signature of a controlled field.** For an *interacting* theory the
domain of analyticity is generically finite. The GFF is entire — no singularities at any
finite complex $z$ — because arbitrarily large smeared fields are exponentially
suppressed by the Gaussian tails of $\mu$. This physical fact is not incidental: it is
*exactly* the estimate that makes the proof go through (see §5).

> **One line:** OS0 is the license to differentiate $Z$ into correlation functions and to
> Wick-rotate — the minimal analytic backbone of a Euclidean QFT.

---

## 3. The central message: a trivial idea in heavy plumbing

This is the one thing to remember about OS0. Read it before the proof, not after.

**The idea (mathematics) is trivial.** By $(\star)$ the generating functional is the
exponential of a bilinear form in the source. So

$$Z\!\Big[\textstyle\sum_i z_i J_i\Big] \;=\; \exp\!\Big(-\tfrac12 \sum_{i,j} z_i z_j\, C_{\mathbb C}(J_i, J_j)\Big),$$

whose exponent is a **quadratic polynomial in $z$**. A polynomial is entire, and $\exp$
of an entire function is entire. That is the complete mathematical content of OS0 — three
words: *exp, quadratic, entire.*

**All the length is bookkeeping.** So why is the file $\approx 700$ lines? Because two
honest measure-theoretic steps stand between $(\star)$ and the display above:

- **Real $\to$ complex.** The measure is *built* with a known characteristic functional
  $(\star)$, but only for **real** sources. OS0 needs complex $z_i$, hence complex $J$.
  Promoting $(\star)$ to complex arguments is a small analytic-continuation argument (the
  **identity theorem**).
- **Differentiation under the integral.** To run that continuation — and to know $Z$ is
  analytic at all — one must differentiate $Z$, *which is an integral*, in its parameter.
  Justifying the **Leibniz rule** for a functional integral requires a single
  $\mu$-integrable **dominating function**. Manufacturing that dominator is where the
  bulk of the file, and the one nontrivial *input* (Fernique's theorem), lives.

So OS0 factors into two short mathematical halves resting on one long plumbing crux:

| Part | What it does | Depth |
|---|---|---|
| **Half A** (§4) | closed form $Z[f] = \exp(-\tfrac12 C_{\mathbb C}(f,f))$ for complex $f$ | short: identity theorem |
| **Half B** (§4) | expand to a quadratic in $z$; $\exp$ of a polynomial is entire | trivial: four lines of glue |
| **Crux** (§5) | $Z$ is differentiable under the integral | *long*: Fernique + Young + Leibniz |

> **One line:** the mathematics is "exp of a quadratic is entire"; the pages are the
> price of differentiating a Gaussian functional integral honestly.

Everything that follows runs under the section variables `{d : ℕ} [Fact (2 ≤ d)]` with a
`[GFFPropagator d m]` instance in scope — the whole argument is dimension-blind (see §6).

---

## 4. Halves A and B — the mathematics (short)

**Half A: the closed form for complex sources.** The target
([OS/OS0_Analyticity.lean:486](../../OSforGFF/OS/OS0_Analyticity.lean#L486)) is

$$Z[f] \;=\; \exp\!\Big(-\tfrac12\, C_{\mathbb C}(f,f)\Big), \qquad C_{\mathbb C}(f,g) = \langle f, C g\rangle, \quad C = (-\Delta + m^2)^{-1}, \tag{A}$$

where $C_{\mathbb C}$ is the **bilinear** (not sesquilinear) complexified covariance form
`freeCovarianceℂ_bilinear`
([OS/Covariance/ParsevalGeneric.lean:163](../../OSforGFF/Covariance/ParsevalGeneric.lean#L163)).
Bilinearity — not the Hermitian inner product — is what lets the exponent become a genuine
polynomial in $z$ in Half B.

The wrinkle: the measure is constructed with a known characteristic functional only for
**real** $f$ (`gff_real_characteristic`,
[OS/Measure/Construct.lean:147](../../OSforGFF/Measure/Construct.lean#L147)), namely
$Z[f] = \exp(-\tfrac12 C(f,f))$. OS0 needs complex $f$. Promote real $\to$ complex by an
identity-theorem argument on a one-parameter slice. Decompose $f = f_{\mathrm{re}} + i\,
f_{\mathrm{im}}$ and, for $t \in \mathbb{C}$, compare

$$L(t) = Z\big[f_{\mathrm{re}} + t\, f_{\mathrm{im}}\big], \qquad R(t) = \exp\!\Big(-\tfrac12\big(Q_{\mathrm{rr}} + 2t\,Q_{\mathrm{ri}} + t^2 Q_{\mathrm{ii}}\big)\Big),$$

with $Q_{\bullet\bullet}$ the real covariance pairings of $f_{\mathrm{re}},
f_{\mathrm{im}}$. Then: (1) $L = R$ for **real** $t$ by the real characteristic
functional; (2) both are **entire** in $t$ — $R$ visibly, and $L$ by the crux §5; (3) the
**identity theorem** (`AnalyticOnNhd.eq_of_frequently_eq`) forces $L = R$ on all of
$\mathbb{C}$ (they agree on $\mathbb{R}$, which accumulates); (4) evaluate at $t = i$ to
recover $f$ and hence (A). So even *writing down* the formula needs an analyticity
argument — a foreshadowing of the axiom itself.

**Half B: the quadratic, and the punchline.** Expand (A) using $\mathbb{C}$-bilinearity
(`freeCovarianceℂ_bilinear_sum_expansion`,
[OS/OS0_Analyticity.lean:618](../../OSforGFF/OS/OS0_Analyticity.lean#L618)):

$$C_{\mathbb C}\!\Big(\textstyle\sum_i z_i J_i,\ \sum_j z_j J_j\Big) = \sum_{i,j} z_i z_j\, C_{\mathbb C}(J_i, J_j),$$

so the closed form for a finite source (`gff_generating_eq_exp_quadratic`,
[OS/OS0_Analyticity.lean:629](../../OSforGFF/OS/OS0_Analyticity.lean#L629)) is

$$Z\!\Big[\textstyle\sum_i z_i J_i\Big] = \exp\!\Big(-\tfrac12 \sum_{i,j} z_i z_j\, C_{\mathbb C}(J_i, J_j)\Big). \tag{B}$$

The exponent is a finite quadratic polynomial in $z$; `analyticOn_finite_quadratic`
([OS/OS0_Analyticity.lean:642](../../OSforGFF/OS/OS0_Analyticity.lean#L642)) certifies it
is analytic (each $z_i$ is a coordinate projection; finite sums and products of analytic
maps are analytic), and the headline `gaussianFreeField_satisfies_OS0`
([OS/OS0_Analyticity.lean:659](../../OSforGFF/OS/OS0_Analyticity.lean#L659)) composes with
$\exp$ in three lines. *This* is the trivial core idea.

> **One line:** the real functional plus the identity theorem give (A); bilinear
> expansion plus "exp of a polynomial is entire" give OS0.

---

## 5. The crux — where the $\approx 700$ lines go

The hard part is not "exp of a quadratic is entire." It is proving that $Z$ — *an
integral* — is even differentiable in its parameter, so that Half A's step (2) is
legitimate. This is `gff_cf_slice_entire`
([OS/OS0_Analyticity.lean:318](../../OSforGFF/OS/OS0_Analyticity.lean#L318)), and it rests
on Mathlib's **Leibniz rule** (`hasFDerivAt_integral_of_dominated_of_fderiv_le`):

$$\frac{d}{dt}\int F(t,\omega)\, d\mu(\omega) \;=\; \int \frac{\partial F}{\partial t}(t,\omega)\, d\mu(\omega),$$

*provided* the $t$-derivative of the integrand is bounded, **uniformly for $t$ in a
ball**, by one **$\mu$-integrable dominating function**. Producing that dominator is the
entire difficulty. (Goursat's theorem then upgrades "complex-differentiable" to
"analytic," yielding the entire slice.)

**The obstruction.** For $F(t,\omega) = e^{\,i\varphi(f_{\mathrm{re}}) + i t\,
\varphi(f_{\mathrm{im}})}$ the norm of the integrand is

$$\big\lVert e^{\,i\langle \omega, f\rangle}\big\rVert = e^{-\varphi(f_{\mathrm{im}})} \tag{C}$$

(`norm_exp_I_distributionPairingℂ_real`,
[OS/OS0_Analyticity.lean:102](../../OSforGFF/OS/OS0_Analyticity.lean#L102)), so over a
ball in $t$ the derivative norm grows like

$$\lvert \varphi(f_{\mathrm{im}})\rvert \; e^{\,\lvert t_{\mathrm{im}}\rvert\, \lvert \varphi(f_{\mathrm{im}})\rvert},$$

an exponential of a *linear* function of the **unbounded** random variable
$\varphi(f_{\mathrm{im}})$. No uniform constant can dominate this.

**The rescue** stitches two classical facts:

- **Fernique's theorem** (`gaussianFreeField_pairing_expSq_integrable`,
  [OS/Measure/Construct.lean:398](../../OSforGFF/Measure/Construct.lean#L398)): for the
  Gaussian GFF measure there is $\alpha > 0$ with $\mathbb{E}[e^{\alpha \varphi(f)^2}] <
  \infty$ — Gaussian tails beat a *quadratic* exponential. This is the one nontrivial
  input, and it is precisely the physical fact (c) of §2.
- **Young's inequality** $c\,\lvert x\rvert \le \tfrac{c^2}{4\alpha} + \alpha x^2$: bound
  the unwanted *linear*-exponential by the Fernique-integrable *quadratic*-exponential.

Together $e^{\,c\lvert x\rvert} \le (\mathrm{const})\cdot e^{\alpha x^2} \in L^1(\mu)$,
and $\lvert x\rvert \le e^{\lvert x\rvert}$ soaks up the polynomial prefactor. A short chain
of lemmas exists solely to assemble this one dominator —
`gff_exp_neg_pairing_integrable`
([:120](../../OSforGFF/OS/OS0_Analyticity.lean#L120)),
and `gff_exp_abs_pairing_memLp`
([:161](../../OSforGFF/OS/OS0_Analyticity.lean#L161)) — consumed inside
`gff_cf_slice_entire`'s differentiation under the integral. Unglamorous — and the reason
analyticity holds. *The Gaussian tails of the free field are exactly what make its
generating functional entire.*

> **One line:** Fernique + Young manufacture one integrable dominator; Leibniz-under-the-
> integral does the rest — that is the whole 700-line detour.

---

## 6. Dimension note — nothing depends on $d$

A striking feature: `OS0_Analyticity.lean` contains **no dimension-specific content** —
it runs under bare `{d : ℕ} [Fact (2 ≤ d)]`. It never names the explicit covariance kernel. The
proof uses only two facts about the theory:

- $C_{\mathbb C}$ is a **$\mathbb{C}$-bilinear form** (Halves A and B), and
- the measure is **Gaussian** (Fernique domination in the crux).

The dimension enters *solely* through the value of the covariance — supplied by the
`GFFPropagator d m` typeclass as a black box — so OS0's proof is genuinely uniform in
$d \ge 2$: written once, instantiated in every dimension. This is
the payoff of the unified library — one proof where the older per-dimension development
kept a separate OS0 file in each directory.

The lower bound $2 \le d$ is not even used here; it rides along from the ambient section
variables and belongs, physically, to OS3 (which needs a time axis).

> **One line:** OS0 is dimension-agnostic — one proof over `[Fact (2 ≤ d)]`, the
> propagator abstracted behind `GFFPropagator d m`.

---

## One-paragraph summary

OS0 asks that the generating functional $Z[\sum_i z_i J_i]$ be entire in $z \in
\mathbb{C}^n$ — equivalently, that all Schwinger functions exist as its $z$-derivatives at
$0$ and that $Z$ is ready for analytic continuation to physical spacetime. For the GFF,
$Z[f] = \exp(-\tfrac12 C_{\mathbb C}(f,f))$ (from the real characteristic functional by an
identity-theorem argument), so $Z[\sum_i z_i J_i]$ is the exponential of a finite
quadratic polynomial in $z$ — manifestly entire. The deep idea is therefore one line; the
$\approx 700$ lines are the rigor behind *differentiating $Z$ under the integral sign* (via
Mathlib's Leibniz rule), which needs a dominating function supplied by **Fernique's
theorem** plus Young's inequality — the Gaussian tails of the free field being precisely
what make $Z$ entire. The proof touches no dimension-specific structure: it runs over
`{d : ℕ} [Fact (2 ≤ d)]` with the propagator hidden behind `GFFPropagator d m`, and one
proof covers every $d \ge 2$.

---

## Pointers into the code

*(All optional — the anchors, not the mathematics, are what you need Lean for.)*

| Result | File | Name (line) |
|---|---|---|
| OS0 axiom (statement) | `OS/Axioms.lean` | `OS0_Analyticity` (76) |
| Bundled OS axioms | `OS/Axioms.lean` | `SatisfiesAllOS` (195) |
| Generating functional (GF) | `Spacetime/Basic.lean` | `GJGeneratingFunctionalℂ` (247) |
| GFF measure / dim-indexed alias | `Measure/Construct.lean` | `gaussianFreeField_free` (134) / `μ_GFF` (139) |
| Real characteristic functional (black box) | `Measure/Construct.lean` | `gff_real_characteristic` (144) |
| Fernique: $e^{\alpha x^2}$ integrable | `Measure/Construct.lean` | `gaussianFreeField_pairing_expSq_integrable` (395) |
| $\lVert e^{i\langle\omega,f\rangle}\rVert = e^{-\varphi(f_{\mathrm{im}})}$ (C) | `OS/OS0_Analyticity.lean` | `norm_exp_I_distributionPairingℂ_real` (112) |
| $e^{-\varphi(f)}$ integrable (Fernique) | `OS/OS0_Analyticity.lean` | `gff_exp_neg_pairing_integrable` (130) |
| $e^{\lvert\varphi(f)\rvert} \in L^p$ (Young + Fernique) | `OS/OS0_Analyticity.lean` | `gff_exp_abs_pairing_memLp` (171) |
| slice is entire (Leibniz / diff. under $\int$) | `OS/OS0_Analyticity.lean` | `gff_cf_slice_entire` (338) |
| $Z[f] = \exp(-\tfrac12 C_{\mathbb C}(f,f))$ (A) | `OS/OS0_Analyticity.lean` | `gff_complex_CF_covariance` (506) |
| bilinear expansion | `OS/OS0_Analyticity.lean` | `freeCovarianceℂ_bilinear_sum_expansion` (638) |
| closed form for $\sum z_i J_i$ (B) | `OS/OS0_Analyticity.lean` | `gff_generating_eq_exp_quadratic` (649) |
| quadratic-form analyticity | `OS/OS0_Analyticity.lean` | `analyticOn_finite_quadratic` (662) |
| complexified covariance form | `Covariance/ParsevalGeneric.lean` | `freeCovarianceℂ_bilinear` (163) |
| **OS0 for the GFF (main)** | `OS/OS0_Analyticity.lean` | `gaussianFreeField_satisfies_OS0` (679) |
| Leibniz rule (imported) | Mathlib `Analysis.Calculus.ParametricIntegral` | `hasFDerivAt_integral_of_dominated_of_fderiv_le` |
| identity theorem (imported) | Mathlib `Analysis.Analytic.Basic` | `AnalyticOnNhd.eq_of_frequently_eq` |

Full auto-generated inventory:
[`../../summary/OSforGFF/OS/OS0_Analyticity.md`](../../summary/OSforGFF/OS/OS0_Analyticity.md).

---

*Companions: [Overview.md](Overview.md) (the OS programme, the master theorem, and the
"length is not depth" table), [OS1OS2.md](OS1OS2.md) (regularity & Euclidean invariance),
[OS3.md](OS3.md) (reflection positivity + the Osterwalder–Schrader reconstruction), and
[OS4.md](OS4.md) (clustering & ergodicity). OS0 supplies the analyticity that the OS3
Hamiltonian later continues from imaginary to real time.*
