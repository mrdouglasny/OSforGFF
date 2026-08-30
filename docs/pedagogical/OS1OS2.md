# OS1 (Regularity) & OS2 (Euclidean Invariance): The Two Light Axioms

*A combined, physics-first walkthrough of the two easiest Osterwalder–Schrader axioms for the
dimension-generic massive Gaussian Free Field (every $d \ge 2$). Written for a reader who knows
Euclidean QFT and functional integrals but not Lean: the mathematics leads, and the Lean names in
`monospace` are just clickable anchors into the formalization — ignore them on a first read.*

---

## The one fact that makes both axioms easy

Everything below rests on a single formula. For a mean-zero Gaussian field, the **generating
(characteristic) functional** is a Gaussian integral you can do in closed form:

$$Z[J] \;:=\; \mathbb{E}\big[e^{\,i\varphi(J)}\big] \;=\; \exp\!\Big(-\tfrac12\,\langle J, C J\rangle\Big).
\tag{G}$$

Read the pieces:

- $\varphi(f) := \langle \omega, f\rangle$ is the **smeared field** — the random field $\omega$
  (a tempered distribution) tested against a Schwartz function $f$, morally $\int \omega(x)\,f(x)\,d^dx$.
  For fixed $f$ it is a Gaussian random variable; the expectation $\mathbb{E}$ is against the GFF
  measure.
- $C = (-\Delta + m^2)^{-1}$ is the **covariance / free propagator**, the two-point function
  $\mathbb{E}[\varphi(f)\varphi(g)] = \langle f, C g\rangle$. In momentum space it is the multiplier
  with symbol $\widehat{C}(k) = 1/(\lvert k\rvert^2 + m^2)$. *Everything* in these two proofs is a
  statement about this one object.

Formula (G) is the hinge: because the field is Gaussian, **each OS axiom collapses into one property
of $C$**. OS1 and OS2 are the two simplest such properties, and they are easy for the *same* reason:

- **OS2 = $C$ is symmetric** (Euclidean-invariant): the propagator sees only distance.
- **OS1 = $C$ is bounded**: the mass gap caps the propagator.

> **One line:** these are the two *light* axioms — OS2 is one line of geometry (a symmetry), OS1 is
> one clean estimate (a boundedness bound). Both are elementary once you see they are just properties
> of $C$, and both hold uniformly for every $d \ge 2$.

Throughout, the free covariance is supplied — uniformly across dimensions — by a `GFFPropagator d m`
typeclass, so no proof below is specialized to a fixed $d$. We do OS2 first (it is shorter and more
transparent), then OS1, then the dimension question, then the cross-axiom "property of $C$" table.

---

## OS2 — Euclidean invariance

### What it says (physics)

The Euclidean world has no preferred origin, orientation, or handedness: correlation functions must
be invariant under the full **Euclidean group** $E(d) = \mathbb{R}^d \rtimes O(d)$ — translations
$t \in \mathbb{R}^d$ combined with rotations and reflections $R \in O(d)$, acting on points by
$g\cdot x = Rx + t$ and on test functions by pullback $(g\cdot f)(x) = f(g^{-1}\cdot x)$. OS2 demands
exactly that the generating functional is unchanged:

$$Z[g\cdot f] = Z[f] \qquad \text{for every } g \in E(d).$$

The precise Lean statement, for anchoring only:

```lean
def OS2_EuclideanInvariance (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (g : QFT.E d) (f : SchwartzTestFunctionℂ d),
    GJGeneratingFunctionalℂ dμ_config f =
    GJGeneratingFunctionalℂ dμ_config (QFT.euclidean_action g f)
```

### The idea (mathematics)

Two clean steps.

**Step 1 — reduce to the covariance (pure Gaussian bookkeeping).** By (G),
$Z[g\cdot f] = \exp(-\tfrac12\,\langle g\cdot f,\, C(g\cdot f)\rangle)$, so $Z[g\cdot f] = Z[f]$ the
moment the covariance *form* is invariant, $\langle g\cdot f, C(g\cdot f)\rangle = \langle f, C f\rangle$.
A general lemma does this reduction once and for all, for *any* Gaussian measure with an invariant
covariance — its only two hypotheses are "the measure is Gaussian" and "its covariance is
Euclidean-invariant" (`gaussian_satisfies_OS2`, fed the fact that the GFF is Gaussian,
`isGaussianGJ_gaussianFreeField_free`). All the GFF-specific work is Step 2.

**Step 2 — the propagator only sees distance (one line of geometry).** This is the heart. The kernel
$C(x, y)$ depends only on $\lVert x - y\rVert$: in momentum space the multiplier is *radial* — it
depends on $k$ only through $\lVert k\rVert$ — so its inverse Fourier transform is a radial profile of
the separation, which is exactly the data the `GFFPropagator` supplies. A Euclidean motion preserves
that distance,

$$\big\lVert (Rx + t) - (Ry + t)\big\rVert = \big\lVert R(x - y)\big\rVert = \lVert x - y\rVert,$$

because $R \in O(d)$ is a linear isometry. Hence $C(g\cdot x, g\cdot y) = C(x, y)$
(`freeCovariance_euclidean_invariant`). Lifting this from the kernel to the bilinear form
(`freeCovarianceℂ_bilinear_euclidean_invariant`) is just a change of variables $x \mapsto g^{-1}\cdot x$,
$y \mapsto g^{-1}\cdot y$: the Euclidean action preserves Lebesgue measure ($\lvert\det R\rvert = 1$,
`measurePreserving_act`), so the two integrals coincide term by term. Specializing to the GFF
two-point function closes it (`CovarianceEuclideanInvariantℂ_μ_GFF`).

> **One line:** OS2 holds because the free propagator is a function of $\lVert x - y\rVert$ alone,
> and isometries preserve $\lVert x - y\rVert$.

---

## OS1 — Regularity (a growth bound)

### What it says (physics)

OS1 is the **temperedness** of the theory: the generating functional may not grow faster than an
exponential of Schwartz seminorms, so that the reconstructed correlation functions are distributions
of *finite order*. Concretely, there must exist $p \in [1, 2]$ and $c > 0$ with

$$\big\lvert Z[f]\big\rvert \;\le\; \exp\!\Big(c\,\big(\lVert f\rVert_{L^1} + \lVert f\rVert_{L^p}^p\big)\Big),$$

plus a side condition that when $p = 2$ the two-point function is locally integrable. The Lean
statement, for anchoring:

```lean
def OS1_Regularity (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∃ (p : ℝ) (c : ℝ), 1 ≤ p ∧ p ≤ 2 ∧ c > 0 ∧
    (∀ (f : SchwartzTestFunctionℂ d),
      ‖GJGeneratingFunctionalℂ dμ_config f‖ ≤
        Real.exp (c * (∫ x, ‖f x‖ ∂volume + ∫ x, ‖f x‖^p ∂volume))) ∧
    (p = 2 → TwoPointIntegrable dμ_config)
```

For the GFF the witnesses are the cleanest possible, $p = 2$ and $c = 1/(2m^2)$
(`gaussianFreeField_satisfies_OS1`), giving the sharp bound

$$\big\lvert Z[f]\big\rvert \;\le\; \exp\!\Big(\tfrac{1}{2m^2}\,\lVert f\rVert_{L^2}^2\Big),$$

which is then weakened into the OS1 shape by adding the nonnegative $L^1$ term inside the exponential.

### The idea (mathematics)

The whole bound is one estimate on the covariance form, in four moves — each one about $C$.

1. **Take the modulus.** From (G), $\lvert e^z\rvert = e^{\mathrm{Re}\,z}$ gives
   $\lvert Z[f]\rvert = \exp\!\big(-\tfrac12\,\mathrm{Re}\,\langle f, C f\rangle\big)$
   (`gff_generating_norm_eq`). The complex covariance form is bilinear, not sesquilinear, so we must
   track its real part honestly.
2. **Drop the good part.** Split $f = f_{\mathrm{re}} + i\,f_{\mathrm{im}}$. Bilinearity gives
   $\mathrm{Re}\,\langle f, C f\rangle = \langle f_{\mathrm{re}}, C f_{\mathrm{re}}\rangle
   - \langle f_{\mathrm{im}}, C f_{\mathrm{im}}\rangle$ (the cross terms carry a factor $i$, hence no
   real part). Since $C$ is positive semidefinite the first term is $\ge 0$, so discarding it can only
   raise the bound: $\lvert Z[f]\rvert \le \exp\!\big(\tfrac12\,\langle f_{\mathrm{im}}, C f_{\mathrm{im}}\rangle\big)$
   (`gff_generating_bound_by_imaginary`).
3. **Go to momentum space (Plancherel).** The covariance form is a momentum integral against its
   multiplier (Parseval, `parseval_covariance_schwartz`):
   $$\langle g, C g\rangle = \int \big\lvert \widehat{g}(k)\big\rvert^2\, P_d(k)\, dk,
   \qquad P_d(k) = \frac{1}{(2\pi)^2\lVert k\rVert^2 + m^2}.$$
   (In prose the multiplier is the schematic $1/(\lvert k\rvert^2 + m^2)$; the code carries an explicit
   $(2\pi)^2$ from its unitary Fourier convention, `freePropagatorMom` — it changes no step below.)
4. **The mass gap caps the multiplier.** Because $m > 0$, the denominator is $\ge m^2$ for every $k$,
   so $P_d(k) \le 1/m^2$ — a one-line algebraic bound. Combined with Plancherel
   $\int \lvert \widehat{g}\rvert^2 = \int \lvert g\rvert^2$ (`fourier_plancherel_schwartz`, no constant
   since the transform is unitary-normalized) and the pointwise $\lvert \mathrm{Im}(f\,x)\rvert \le \lVert f\,x\rVert$,
   this yields $\langle f_{\mathrm{im}}, C f_{\mathrm{im}}\rangle \le \tfrac{1}{m^2}\lVert f\rVert_{L^2}^2$
   (`covariance_imaginary_L2_bound`), hence the pure $L^2$ bound with $c = 1/(2m^2)$
   (`gff_generating_L2_bound`).

The $p = 2$ side condition is discharged uniformly in $d$: the two-point function agrees almost
everywhere with the centered covariance kernel (they differ only at the origin, a null set), and that
kernel is *globally* $L^1$ straight from the propagator's built-in integrability
(`gff_two_point_locally_integrable`). Local integrability is then immediate — no dimension-sensitive
$\lVert x\rVert^{-\alpha}$ estimate is needed.

> **One line:** OS1 holds because $C$ is the Fourier multiplier $1/(\lvert k\rvert^2 + m^2)$, bounded
> by $1/m^2$ — the mass gap turns "$\le$ the $L^2$ norm" into the growth bound.

---

## Dimension note

Both axioms are **uniform in $d \ge 2$**, like every axiom in the library.
The proofs sit in the `OS/` directory only because they mention the $d$-baked spacetime and test-function
types, not because the mathematics changes:

- **OS2** is *fully* agnostic: it uses only that the multiplier is radial and that isometries preserve
  distance — true in every dimension.
- **OS1**'s growth bound is agnostic too: Plancherel and the algebraic bound
  $1/(\lvert k\rvert^2 + m^2) \le 1/m^2$ hold in any $d$ and need only $m > 0$. Even the $p = 2$ side
  condition is dimension-uniform now: it rides on the global $L^1$-integrability of the radial
  covariance profile packaged in the `GFFPropagator`, transported almost everywhere off the null set
  $\{0\}$, rather than on a dimension-dependent local-integrability argument.

So OS1 and OS2 hold verbatim, with the identical proof term, for every `[GFFPropagator d m]` instance
in the library (any $d \ge 2$; closed forms at $d = 2, 3, 4, 5$).

---

## The unifying picture: every axiom is a property of $C$

Because the field is Gaussian and $Z[f] = \exp(-\tfrac12\langle f, C f\rangle)$, each Osterwalder–Schrader
axiom is exactly one property of the single covariance $C = (-\Delta + m^2)^{-1}$:

| Axiom | Property of $C$ | Mechanism | Idea vs. length |
|---|---|---|---|
| **OS0** Analyticity | $C$ is a **bilinear form** | $\exp$ of a quadratic is entire (+ Fernique) | trivial idea, long — `OS0.md` |
| **OS1** Regularity | $C$ is **bounded** ($\le \tfrac{1}{m^2}\lVert\cdot\rVert_{L^2}^2$) | Plancherel + mass-gap multiplier bound | light idea, short — *this note* |
| **OS2** Invariance | $C$ is **symmetric** (Euclidean) | propagator sees only $\lVert x - y\rVert$ | light idea, short — *this note* |
| **OS3** Reflection positivity | reflected $C$ is **positive** | mixed representation + Schur–Hadamard | deep idea, long — `OS3.md` |
| **OS4** Clustering/ergodicity | $C$ **decays** | exponential decay from the mass gap | one real idea + long estimate — `OS4.md` |

Read top to bottom: $C$ is a bounded, symmetric, reflection-positive, decaying bilinear form. OS1 and
OS2 are the two light rows because *boundedness* and *symmetry* are one estimate and one isometry —
whereas *positivity* (OS3) and *decay* (OS4) demand real structural or quantitative work. And all five
trace back, through the mass $m > 0$, to the same denominator $\lVert k\rVert^2 + m^2$.

---

## One-paragraph summary

For the dimension-generic GFF, $Z[f] = \exp(-\tfrac12\langle f, C f\rangle)$, so OS2 and OS1 are two
facts about the one covariance $C$. **OS2** is symmetry: $C$ depends only on $\lVert x - y\rVert$,
isometries preserve that distance, and a measure-preserving change of variables makes the covariance
form — hence $Z$ — Euclidean-invariant. **OS1** is boundedness: taking the modulus leaves
$\exp(-\tfrac12\,\mathrm{Re}\langle f, C f\rangle)$, positivity lets us drop the real part and keep the
imaginary, and in momentum space the multiplier $1/(\lvert k\rvert^2 + m^2) \le 1/m^2$ plus Plancherel
gives $\lvert Z[f]\rvert \le \exp(\tfrac{1}{2m^2}\lVert f\rVert_{L^2}^2)$, i.e. OS1 with $p = 2$,
$c = 1/(2m^2)$. Both proofs are identical across $d \ge 2$.

---

## Pointers into the code

| Result | File | Name (line) |
|---|---|---|
| OS1 axiom (statement) | `OS/Axioms.lean` | [`OS1_Regularity`](../../OSforGFF/OS/Axioms.lean#L86) (86) |
| two-point integrability (side condition) | `OS/Axioms.lean` | [`TwoPointIntegrable`](../../OSforGFF/OS/Axioms.lean#L82) (82) |
| OS2 axiom (statement) | `OS/Axioms.lean` | [`OS2_EuclideanInvariance`](../../OSforGFF/OS/Axioms.lean#L94) (94) |
| **OS1 for the GFF (main)** | `OS/OS1_Regularity.lean` | [`gaussianFreeField_satisfies_OS1`](../../OSforGFF/OS/OS1_Regularity.lean#L404) (404) |
| modulus $\lvert Z\rvert = \exp(-\tfrac12\mathrm{Re}\langle f, C f\rangle)$ | `OS/OS1_Regularity.lean` | [`gff_generating_norm_eq`](../../OSforGFF/OS/OS1_Regularity.lean#L150) (150) |
| drop the positive real part | `OS/OS1_Regularity.lean` | [`gff_generating_bound_by_imaginary`](../../OSforGFF/OS/OS1_Regularity.lean#L160) (160) |
| imaginary form $\le \tfrac{1}{m^2}\lVert f\rVert_{L^2}^2$ | `OS/OS1_Regularity.lean` | [`covariance_imaginary_L2_bound`](../../OSforGFF/OS/OS1_Regularity.lean#L236) (236) |
| final $L^2$ growth bound | `OS/OS1_Regularity.lean` | [`gff_generating_L2_bound`](../../OSforGFF/OS/OS1_Regularity.lean#L368) (368) |
| two-point locally integrable (uniform in $d$) | `OS/OS1_Regularity.lean` | [`gff_two_point_locally_integrable`](../../OSforGFF/OS/OS1_Regularity.lean#L386) (386) |
| Plancherel | `OS/OS1_Regularity.lean` | [`fourier_plancherel_schwartz`](../../OSforGFF/OS/OS1_Regularity.lean#L62) (62) |
| covariance = momentum integral (Parseval) | `Covariance/ParsevalGeneric.lean` | [`parseval_covariance_schwartz`](../../OSforGFF/Covariance/ParsevalGeneric.lean#L577) (577) |
| momentum multiplier $P_d(k)$ | `Covariance/Propagator.lean` | [`freePropagatorMom`](../../OSforGFF/Covariance/Propagator.lean#L55) (55) |
| **OS2 for the GFF** (covariance invariance) | `OS/OS2_Invariance.lean` | [`CovarianceEuclideanInvariantℂ_μ_GFF`](../../OSforGFF/OS/OS2_Invariance.lean#L152) (152) |
| bilinear-form invariance | `OS/OS2_Invariance.lean` | [`freeCovarianceℂ_bilinear_euclidean_invariant`](../../OSforGFF/OS/OS2_Invariance.lean#L112) (112) |
| kernel invariance $C(gx, gy) = C(x, y)$ | `Covariance/ParsevalGeneric.lean` | [`freeCovariance_euclidean_invariant`](../../OSforGFF/Covariance/ParsevalGeneric.lean#L654) (654) |
| Lebesgue-preserving Euclidean action | `Spacetime/Euclidean.lean` | [`measurePreserving_act`](../../OSforGFF/Spacetime/Euclidean.lean#L241) (241) |
| Gaussian + invariant covariance ⇒ OS2 (general) | `Measure/GaussianFreeField.lean` | [`gaussian_satisfies_OS2`](../../OSforGFF/Measure/GaussianFreeField.lean#L62) (62) |
| GFF is Gaussian (feeds the wrapper) | `Measure/IsGaussian.lean` | [`isGaussianGJ_gaussianFreeField_free`](../../OSforGFF/Measure/IsGaussian.lean#L534) (534) |
| master theorem (bundles all six) | `OS/Master.lean` | [`gaussianFreeField_satisfies_all_OS_axioms_generic`](../../OSforGFF/OS/Master.lean#L61) (61) |

For the full theorem inventories see the auto-generated summaries
[`../../summary/OSforGFF/OS/OS1_Regularity.md`](../../summary/OSforGFF/OS/OS1_Regularity.md) and
[`../../summary/OSforGFF/OS/OS2_Invariance.md`](../../summary/OSforGFF/OS/OS2_Invariance.md).

---

*Companions: Overview.md (the covariance and the master theorem), OS0.md (analyticity), OS3.md
(reflection positivity & OS reconstruction), OS4.md (clustering & ergodicity). Together these cover
all five Osterwalder–Schrader axioms for the dimension-generic massive Gaussian Free Field.*
