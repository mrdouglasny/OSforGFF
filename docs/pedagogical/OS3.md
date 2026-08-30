# OS3 — Reflection Positivity: the Euclidean shadow of unitarity

*A physics-first walkthrough of the deepest and longest of the Osterwalder–Schrader
axioms for the unified, dimension-generic Gaussian Free Field (every $d \ge 2$).
Written for someone who knows Euclidean QFT and functional integrals but not Lean:
the mathematics leads, and the Lean names in `monospace` with `:NNN` line links are
just clickable anchors into the formalization that you can ignore.*

Everything below is a statement about **one object**, the free massive propagator, and
about **one measure** on field configurations built from it. A 30-second dictionary of
the objects, then straight into the physics:

- **Field configuration** $\omega$ — a tempered distribution; a "random field," the
  point of the probability space.
- **Smeared field** $\varphi(f) := \langle \omega, f\rangle$ — the field tested against a
  Schwartz function $f$, morally $\int \omega(x)\, f(x)\, d^d x$. For a *fixed* $f$ this is a
  **Gaussian random variable**; $\varphi(\theta f)$ below is just the field smeared against
  the reflected test function.
- **The measure** $\mu \equiv \mu_{\mathrm{GFF}}\, d\, m$ — the mean-zero Gaussian measure
  on field configurations with covariance $C$ (built by Minlos). Expectations $\mathbb{E}$
  are against $\mu$.
- **Covariance / propagator** $C = (-\Delta + m^2)^{-1}$, the two-point function
  $\mathbb{E}[\varphi(f)\,\varphi(g)] = \langle f, C g\rangle$, with momentum-space symbol
  $\widehat{C}(k) = 1/(\lvert k\rvert^2 + m^2)$.
- **Generating (characteristic) functional** $Z[J] := \mathbb{E}\big[e^{\,i\varphi(J)}\big]$.
  Because $\mu$ is Gaussian,
  $$Z[J] \;=\; \exp\!\Big(-\tfrac12\,\langle J, C J\rangle\Big). \tag{$\star$}$$
  Read every line of this note as "some property of $C$, seen through $(\star)$."
- **Time reflection** $\theta$ and **positive time.** Split spacetime $x = (x_0, \bar x)$
  into a time coordinate $x_0 \in \mathbb{R}$ and space $\bar x \in \mathbb{R}^{d-1}$; then
  $\theta(x_0, \bar x) = (-x_0, \bar x)$, acting on test functions by $(\theta f)(x) = f(\theta x)$.
  A **positive-time** test function is supported in $\{x_0 > 0\}$. The split needs a time
  axis — that is where the permanent lower bound $d \ge 2$ comes from.

The field is `gaussianFreeField_free (d := d) m` (the measure `μ_GFF d m`), the covariance
is the radial kernel `freeCovariance d m`, and the dimension is a silent parameter; the
closing dimension note explains why no upper bound on $d$ is needed.

---

## What OS3 says, and the idea behind it

**What it says (physics).** Reflection positivity is the Euclidean fingerprint of
*unitarity*. It is exactly the positivity that lets Osterwalder–Schrader reconstruction
build a physical Hilbert space of states with a genuine (positive) inner product and a
self-adjoint Hamiltonian $H \ge 0$ generating time evolution. Concretely, for any finite
family of positive-time test functions $f_1, \dots, f_n$ and coefficients
$c \in \mathbb{C}^n$, the $n \times n$ matrix

$$M_{jk} \;=\; Z\!\left[\, f_j - \mathrm{star}\, f_k \,\right],
\qquad (\mathrm{star}\, f)(x) = \overline{f(\theta x)}, \tag{RP}$$

must be **positive semidefinite (PSD)**: $c^{*} M c \ge 0$. The `star` operation folds
together time reflection $\theta$ and complex conjugation — the conjugation is forced by
the $i$ in the characteristic function $e^{i\varphi}$, since
$M_{jk} = \mathbb{E}\big[\,\overline{e^{i\varphi(f_j)}}\; e^{i\varphi(f_k)}\,\big]
= \mathbb{E}\big[\,e^{i\varphi(\theta f_j)}\, e^{i\varphi(f_k)}\,\big]$.
In the formalization this is the predicate the master theorem consumes
([OS/Axioms.lean:112](../../OSforGFF/OS/Axioms.lean#L112)):

```lean
def OS3_ReflectionPositivity (dμ_config : ProbabilityMeasure (FieldConfiguration d)) : Prop :=
  ∀ (n : ℕ) (f : Fin n → PositiveTimeTestFunctionℂ d) (c : Fin n → ℂ),
    0 ≤ (∑ i, ∑ j, starRingEnd ℂ (c i) * c j *
      GJGeneratingFunctionalℂ dμ_config
        ((f i).val - star ((f j).val))).re
```

**The idea (mathematics).** Two genuine mathematical ideas, stacked on top of each other:

1. **A mixed representation to expose a factorizing exponential.** The naive move — write
   $\langle \theta f, C f\rangle$ in momentum space and stare — *fails*: doing the
   time-momentum integral first leaves a spatial kernel $\sim 1/\sqrt{\lvert \bar k\rvert^2 + m^2}$
   that is **not absolutely integrable**, so none of the integral interchanges the argument
   needs are licensed. The fix is to Fourier transform **only the spatial** directions and
   keep time in position space, via a proper-time (Schwinger) integral. The time kernel then
   becomes a **pure exponential** $\tfrac{1}{2\omega}\, e^{-\omega\lvert x_0 + y_0\rvert}$,
   $\omega = \sqrt{\lvert \bar k\rvert^2 + m^2}$. At positive times it factorizes,
   $e^{-\omega(x_0 + y_0)} = e^{-\omega x_0}\, e^{-\omega y_0}$, turning
   $\langle \theta f, C f\rangle$ into a manifest sum of squared moduli $\ge 0$ — reflection
   positivity *of the covariance*.
2. **The Schur–Hadamard lift.** Positivity of the scalar $\langle \theta f, C f\rangle$ must
   be promoted to positive-semidefiniteness of the whole matrix (RP). Because the field is
   Gaussian, $(\star)$ gives $M_{jk} = A_j\, \overline{A_k}\, e^{R_{jk}}$ with
   $R_{jk} = \langle \theta f_j, C f_k\rangle$ PSD; and the **entrywise exponential of a PSD
   matrix is PSD** ($e^{R} = \sum_n R^{\odot n}/n!$, each Hadamard power PSD by the Schur
   product theorem). That is real positivity theory, not bookkeeping.

Headline `QFT.gaussianFreeField_OS3`
([OS/OS3_ReflectionPositivity.lean:989](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L989)),
plugged into the `os3` field of the master theorem
`gaussianFreeField_satisfies_all_OS_axioms_generic`
([OS/Master.lean:61](../../OSforGFF/OS/Master.lean#L61)).

> **One line:** OS3 says the reflected generating-functional matrix is PSD — the seed of a
> positive quantum norm; expose a factorizing exponential by a mixed representation, then
> lift scalar positivity to matrix positivity by Schur–Hadamard.

---

## Why OS3 is the *deep* axiom (length is not depth)

The other pedagogical notes hammer a distinction worth repeating: a formalization's *length*
measures how much measure-theoretic and analytic bookkeeping it must carry, not how deep the
underlying idea is. OS0, for instance, is $\approx 700$ lines built on a *trivial* idea
("$\exp$ of a quadratic is entire") wrapped in analytic plumbing — long but shallow.

**OS3 is the opposite: it is hard mathematics *and* long.** Its $\approx 6{,}750$ lines
across four files (more than OS0, OS1, OS2, OS4 combined) carry two real ideas — the mixed
(proper-time) representation that manufactures the factorizing exponential, and the
entrywise-exponential positivity theory (Schur–Hadamard) that lifts scalar positivity to
the matrix (RP). Neither is bookkeeping; each is the kind of maneuver a working
constructive field theorist would recognize as *the* content. But those ideas sit on top of
a genuinely large technical layer: a Fubini/integrability foundation ($\approx 3{,}620$
lines, the file `OS3_MixedRepInfra`) whose only job is to make every integral interchange in
the mixed representation *legal*. So OS3 is deep **and** heavy — the ideas are worth the
length, and the length is not padding. It is also, not coincidentally, *the* Osterwalder–
Schrader reconstruction positivity: the axiom whose whole purpose is to guarantee a positive
quantum norm (final section).

---

## The shape of the whole argument

The four files form a **linear pipeline** (each building on the layers below it) and
handing one theorem up. You can read the ideas top to bottom without ever opening the Lean;
the anchors are here for when you do.

```
  OS3_MixedRepInfra       (3620 lines)   analytic foundation: integrals converge
          │                              (heat kernel, Schwinger rep, Fubini swaps)
          │   integrable_dominate_G · fubini_s_ksp_swap
          ▼
  OS3_MixedRep            (1488 lines)   the MIXED REPRESENTATION of ⟨θf, C f⟩
          │                              (spatial Fourier transform, time kept)
          │   bessel_bilinear_eq_mixed_representation
          ▼
  OS3_CovarianceRP         (468 lines)   reflection positivity of the COVARIANCE
          │                              (⟨θf, C f⟩ ≥ 0)
          │   freeCovariance_reflection_positive_bilinear / _real
          ▼
  OS3_ReflectionPositivity(998 lines)   lift covariance-RP to the MEASURE
          │                              (Schur–Hadamard ⇒ matrix (RP) is PSD)
          │   gaussianFreeField_OS3_real → gaussianFreeField_OS3
          ▼
     QFT.gaussianFreeField_OS3           ← the axiom, consumed by OS/Master.lean
```

The single mathematical seed at the heart is tiny:

> **A reflected exponential factorizes:** $e^{-\omega(s+t)} = e^{-\omega s}\, e^{-\omega t}$.

Almost everything else is the cost of (a) reaching that exponential *rigorously* and
(b) lifting the resulting scalar inequality to the full Gaussian measure. The next four
sections unpack each layer, foregrounding the physics in each.

---

## 1. The propagator as a proper-time integral (`OS3_MixedRepInfra`)

**What it says (physics).** The whole file establishes one enabling fact: the massive
propagator can be written as a Schwinger (proper-time / heat-kernel) integral, and *because
of that*, every integral the mixed representation wants to interchange is absolutely
convergent. No reflection positivity appears here — this is the analytic groundwork.

**The idea (mathematics).** In momentum space $\widehat{C}(p) = 1/(\lvert p\rvert^2 + m^2)$.
Doing the naive time-momentum integral first leaves a spatial factor
$1/\sqrt{\lvert \bar k\rvert^2 + m^2}$ that is not absolutely integrable in the
$(d-1)$-dimensional $\bar k$ — so the naive Fourier proof is not licensed. The device that
routes around this is the identity

$$\frac{1}{\lvert p\rvert^2 + m^2} = \int_0^\infty e^{-s(\lvert p\rvert^2 + m^2)}\, ds, \tag{Schwinger}$$

trading the propagator for a Gaussian integrated over a "proper time" $s > 0$. On the
position side this is the mass-damped heat kernel,

$$C_d(r) = \int_0^\infty e^{-s m^2}\, H_d(s, r)\, ds,
\qquad H_d(s, r) = (4\pi s)^{-d/2}\, e^{-r^2/(4s)},$$

which is exactly the `schwinger_eq` field of the `GFFPropagator d m` typeclass — *one*
uniform formula for every $d$. Because $H_d(s, \cdot)$ is bounded for each fixed $s > 0$,
Schwartz functions are bounded, and $e^{-s m^2}$ decays, the reflected pairing

$$\langle \theta f, C f\rangle = \int_0^\infty e^{-s m^2}
\Big[\iint \overline{f(x)}\, f(y)\, H_d\big(s, \lVert \theta x - y\rVert\big)\Big]\, ds$$

is built from absolutely convergent integrals. The file's job is to certify exactly that:

- [`heatKernel_eq_gaussianFT`](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L186) — $H_d(s, \cdot)$
  is the (inverse) Gaussian Fourier transform;
- a stack of Tonelli/Fubini lemmas
  ([`schwinger_bound_integrable_fubini`](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L603),
  [`schwinger_bound_integrable`](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L717)) showing every
  integrand the next file reorders is absolutely convergent;
- the **domination lemma** [`integrable_dominate_G`](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L858)
  and the proper-time / spatial-momentum swap
  [`fubini_s_ksp_swap`](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L2650) — the two crucial
  exchanges (dimension note).

The dominating function is
[`dominate_G`](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L847),
$(s, \bar k) \mapsto C\, s^{d+1/2}\, e^{-s(\lVert \bar k\rVert^2 + m^2)}$. The power $s^{d+1/2}$
is the **order-$d$ vanishing** of positive-time test functions at the time boundary,
$\lVert f(x)\rVert \lesssim x_0^d$, after the odd time-Gaussian moment
$\int_0^\infty u^{2d+1} e^{-u^2/4s}\, du = (d!/2)(4s)^{d+1}$
([`integral_odd_pow_gaussian`](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L1354)). That
$s$-power is what keeps the domination integrable in **every** dimension (dimension note).

> **One line:** the propagator is a proper-time integral of Gaussians — and *that* is what
> makes every subsequent integral interchange absolutely convergent.

---

## 2. The mixed representation (`OS3_MixedRep`)

**What it says (physics).** This is the mathematical heart: the reflected two-point form
$\langle \theta f, C f\rangle$ is rewritten as a spatial-momentum integral whose kernel in
the *time* variables is a **bare exponential** — the manifestly relativistic form in which
each spatial mode $\bar k$ carries the energy $\omega = \sqrt{\lVert \bar k\rVert^2 + m^2}$.

**The idea (mathematics).** Fourier transform **only the spatial** directions
$\bar x \in \mathbb{R}^{d-1}$, keeping the time $x_0$ explicit, and do the two Gaussian/Laplace
integrals the proper-time representation exposes. The chain performs the interchanges
licensed in file 1:

```
  heatKernel_bilinear_fourier_form   (insert Gaussian FT of H_d, do the k₀ integral)
     → fubini_ksp_xy_swap / fubini_s_xy_swap   (interchange s, k̄, and x,y integrals)
     → laplace_s_integral_with_norm    (do the s-Laplace integral)
     → heatKernel_bilinear_to_mixed_rep  (spatial FT; time stays)
     → bessel_bilinear_eq_mixed_representation   (final mixed form)
```

Two evaluations do the work. The **time-momentum $k_0$ Gaussian** collapses to
$\int e^{-i k_0 t}\, e^{-s k_0^2}\, dk_0 = \sqrt{\pi/s}\; e^{-t^2/4s}$, and the **proper-time
Laplace integral** then collapses to
$\int_0^\infty \sqrt{\pi/s}\; e^{-t^2/4s}\, e^{-s\omega^2}\, ds = \tfrac{\pi}{\omega}\, e^{-\omega\lvert t\rvert}$.
The clean end result
([`bessel_bilinear_eq_mixed_representation`](../../OSforGFF/OS/OS3_MixedRep.lean#L1467)) is

$$\langle \theta f, C f\rangle = \frac{1}{2(2\pi)^{d-1}} \int_{\bar k} \iint
\overline{f(x)}\, f(y)\; \frac{1}{\omega}\, e^{-\omega\lvert x_0 + y_0\rvert}\;
e^{-i\,\bar k\cdot(\bar x - \bar y)}\; d\bar k\, dx\, dy, \tag{MR}$$

with $\omega = \omega_{\bar k} = \sqrt{\lVert \bar k\rVert^2 + m^2}$ the **relativistic
energy** of the spatial momentum $\bar k$. (The reflection $\theta$ turned the time argument
of $H_d$ into that of $\theta x - y$, whose time component is $-x_0 - y_0$; hence the
$\lvert x_0 + y_0\rvert$.)

Two features of (MR) are the entire point:

1. The normalization $\frac{1}{(2\pi)^d}\cdot \pi = \frac{1}{2(2\pi)^{d-1}}$ is proved inline
   for arbitrary $d$. The radial spatial integral is where the dimension-specific Bessel
   closed form *would* live ($K_0$ at $d = 2$, Yukawa at $d = 3$, $K_1$ at $d = 4$, $K_{3/2}$
   at $d = 5$) — but OS3 never needs the closed form, only this generic identity.
2. The **time kernel $\tfrac{1}{2\omega}\, e^{-\omega\lvert x_0 + y_0\rvert}$ is a pure
   exponential** in the times. *That* is what makes reflection positivity work in the next
   file. Everything below Section 2 exists to reach this exponential honestly.

> **One line:** Fourier the space, keep the time — the covariance becomes a spatial integral
> whose time kernel is a bare exponential $e^{-\omega\lvert x_0 + y_0\rvert}$.

---

## 3. Reflection positivity of the covariance (`OS3_CovarianceRP`)

**What it says (physics).** Restrict to positive-time test functions. Then the bare
exponential factorizes across the reflection, and the reflected two-point form becomes a
manifest sum of squared moduli: $\langle \theta f, C f\rangle \ge 0$. This is reflection
positivity at the level of the *one-particle* (covariance) structure.

**The idea (mathematics).** On positive-time support $x_0, y_0 \ge 0$, so
$\lvert x_0 + y_0\rvert = x_0 + y_0$
([`RPProof.abs_neg_sum_nonneg`](../../OSforGFF/OS/OS3_CovarianceRP.lean#L146)) and the miracle
is a single line:

$$e^{-\omega(x_0 + y_0)} = e^{-\omega x_0}\, e^{-\omega y_0}. \tag{FACT}$$

Feed (FACT) into (MR): the double $(x, y)$ integral **separates** into an $x$-factor and a
$y$-factor
([`RPProof.factorization_to_squared_norm_direct`](../../OSforGFF/OS/OS3_CovarianceRP.lean#L241)),
each equal (up to the sign of $\bar k$) to the **weighted Laplace–Fourier transform**

$$F_\omega(\bar k) = \int f(x)\, e^{-\omega x_0}\, e^{-i\,\bar k\cdot\bar x}\, dx.$$

A kernel of the form $g\,\overline{g}$ is rank one and manifestly positive, so the inner
double integral collapses to a squared modulus and

$$\langle \theta f, C f\rangle = \frac{1}{2(2\pi)^{d-1}} \int_{\bar k}\;
\frac{1}{\omega}\, \big\lvert F_\omega(-\bar k)\big\rvert^2\, d\bar k \;\ge\; 0 \tag{RP-cov}$$

([`RPProof.rp_equals_squared_norm_integral`](../../OSforGFF/OS/OS3_CovarianceRP.lean#L335)):
both the prefactor and the integrand $\tfrac{1}{\omega}\lvert F_\omega\rvert^2$ are
non-negative. This is exported through the complex/real bridge lemmas:

- [`freeCovariance_reflection_positive_bilinear`](../../OSforGFF/OS/OS3_CovarianceRP.lean#L412)
  — $0 \le \mathrm{Re}\,\langle \theta f, C f\rangle$ for complex positive-time $f$;
- [`freeCovariance_reflection_positive_real`](../../OSforGFF/OS/OS3_CovarianceRP.lean#L463)
  — $0 \le \iint (\theta f)(x)\, C(x, y)\, f(y)$ for real positive-time $f$.

What we have so far is a statement about a *single* quadratic form. OS3 (RP) is about an
entire *matrix* of generating-functional values — bridging that gap is the last file.

> **One line:** positive time forces $\lvert x_0 + y_0\rvert = x_0 + y_0$, the exponential
> splits, and $\langle \theta f, C f\rangle$ becomes a sum of squared moduli — hence $\ge 0$.

---

## 4. From covariance to measure: the Schur–Hadamard lift (`OS3_ReflectionPositivity`)

**What it says (physics).** The measure-level statement (RP) is about the full generating
functional, not just the two-point form. For a Gaussian field, though, everything is the
exponential of the covariance — so matrix positivity of $M$ follows from matrix positivity
of the reflected covariance $R$ by a purely linear-algebra fact about entrywise
exponentials. This is where "$R$ is PSD" becomes "$M$ is PSD," and it is exactly the passage
from one-particle positivity to Fock-space positivity.

**The idea (mathematics).** By $(\star)$, $Z[h] = \exp(-\tfrac12\langle h, C h\rangle)$;
expanding the argument $f_j - \mathrm{star}\, f_k$ of (RP), every matrix entry factors as

$$M_{jk} = A_j\, \overline{A_k}\; \exp\!\big(R_{jk}\big),
\qquad A_j = \exp\!\big(-\tfrac12\langle f_j, C f_j\rangle\big), \tag{ENTRY}$$

where $R_{jk} = \langle \theta f_j, C f_k\rangle$ is the **reflected covariance matrix**
([`gaussianFreeField_real_entry_factor`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L341),
[`gff_complexZ_entry_factor`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L828)). From
Section 3, $R$ is PSD (take $F = \sum_j c_j f_j$, still positive-time, and apply (RP-cov)):
this is
[`freeCovarianceFormR_reflection_matrix_posSemidef`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L93)
in the real case, and
[`reflection_matrix_IsRePSD`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L914) (with
Hermiticity from
[`reflection_matrix_IsHermitian`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L633)) in
the complex case.

Conjugation by the diagonal $D = \mathrm{diag}(A_j)$ preserves PSD, so (ENTRY) reduces OS3
to a single linear-algebra question:

> Given a PSD matrix $R$, is its **entrywise exponential** $(e^{R_{jk}})_{jk}$ PSD?

**Yes** — and that is the Schur–Hadamard argument.

### 4.1 The Schur product theorem

> **Theorem (Schur, 1911).** If $A$ and $B$ are PSD, so is the entrywise (Hadamard) product
> $(A \circ B)_{jk} = A_{jk}\, B_{jk}$.

The clean proof uses Gram factorizations: any PSD matrix is a Gram matrix,
$A_{jk} = \langle u_j, u_k\rangle$, $B_{jk} = \langle v_j, v_k\rangle$, and

$$(A \circ B)_{jk} = \langle u_j, u_k\rangle\, \langle v_j, v_k\rangle
= \langle\, u_j \otimes v_j,\; u_k \otimes v_k \,\rangle$$

is again a Gram matrix, hence PSD. The formalization realizes this directly
([`posSemidef_hadamard_complex`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L707)): the
Hadamard product is the diagonal `submatrix` of the `kronecker` product, and PSD is preserved
by both.

### 4.2 Hadamard powers and the entrywise exponential

Iterating Schur, every **Hadamard power** $R^{\circ n} = R \circ \cdots \circ R$ ($n$
factors) of a PSD $R$ is PSD. PSD matrices form a **closed convex cone** — closed under
addition and non-negative scaling — so any convergent non-negative combination of Hadamard
powers is PSD. Applying the scalar series $e^x = \sum_n x^n/n!$ entrywise,

$$\big(e^{R_{jk}}\big)_{jk} = \sum_{n=0}^{\infty} \frac{1}{n!}\, R^{\circ n}, \tag{HEXP}$$

every term is PSD times $1/n! > 0$, and a convergent sum of PSD matrices is PSD. Hence:

> **Corollary.** If $R$ is PSD, its entrywise exponential $(e^{R_{jk}})_{jk}$ is PSD.

This is
[`entrywiseExp_posSemidef_of_posSemidef`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L74)
(real, via the imported
`OSforGFF.posSemidef_entrywiseExp_hadamardSeries_of_posSemidef`) and
[`entrywiseExp_IsRePSD`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L724) (complex, taking
limits of the partial sums of (HEXP) inside the closed PSD cone).

### 4.3 Closing OS3

Combining (ENTRY) with the corollary, $M = D\,(e^{R_{jk}})\, D^{*}$ with
$D = \mathrm{diag}(A_j)$: the entrywise exponential is PSD, conjugation preserves PSD, so $M$
is PSD — which is exactly OS3 (RP). The assembly is

```
  gaussianFreeField_OS3_matrix_real → gaussianFreeField_OS3_real     (real form)
  gff_complexOS3_matrix            → gaussianFreeField_OS3           (complex (star) form)
```

and `OS/Master.lean` plugs
[`QFT.gaussianFreeField_OS3`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L989) (with the
real version [`gaussianFreeField_OS3_real`](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L500))
into the `os3` field of the generic master theorem, whence the concrete headlines
`SatisfiesAllOS (μ_GFF 2 m)`, …, `SatisfiesAllOS (μ_GFF 5 m)`.

**Why "Gaussian" is essential:** only for a Gaussian measure does the generating functional
become the *exponential* of the covariance (ENTRY). That is what turns "$R$ is PSD" into
"$M$ is PSD" through the entrywise exponential. For a non-Gaussian field there is no such
clean factorization and Schur–Hadamard does not apply directly.

> **One line:** each Gaussian matrix entry is $e^{R_{jk}}$; the entrywise exponential of a
> PSD matrix is PSD (Schur ⇒ Hadamard powers ⇒ series), so the whole matrix is PSD.

---

## 5. Why OS3 is the *right* axiom: Hilbert-space positivity

Everything above proves a positivity statement, but *why that statement?* OS3 is the
**Euclidean fingerprint of a positive-definite quantum Hilbert space**. This section sketches
the Osterwalder–Schrader reconstruction that OS3 enables, then identifies, for the GFF,
exactly which vectors have zero norm.

### 5.1 A Euclidean field has no Hilbert space yet

The GFF lives on a *probability space*; the only inner product in sight is the $L^2(\mu)$
one, $\langle F, G\rangle = \mathbb{E}[\overline{F}\, G]$. That is a fine Hilbert space, but
**not** the state space of a quantum theory: it treats all of Euclidean spacetime
symmetrically, with no distinguished time, no Hamiltonian, no unitary dynamics. Quantum
mechanics needs a space $\mathcal{H}_{\mathrm{phys}}$ carrying a self-adjoint $H \ge 0$ that
generates time evolution. OS3 is exactly the condition that lets you *build* it.

### 5.2 The reflected pre-inner-product; OS3 = positivity

Let $\mathcal{E}_+$ be the algebra of functionals supported at **positive time** (e.g.
products $e^{i\varphi(f_1)}\cdots e^{i\varphi(f_n)}$ with each $f_j$ supported in
$\{x_0 > 0\}$), and let $\theta$ act on functionals by time reflection. Define a **new**
sesquilinear form — not the naive $L^2$ one, but with a reflection inserted:

$$(F, G)_{\mathrm{phys}} \;:=\; \mathbb{E}\!\left[\,\overline{\theta F}\;\, G\,\right].$$

Taking $F = \sum_j c_j\, e^{i\varphi(f_j)}$ with positive-time $f_j$,

$$(F, F)_{\mathrm{phys}} = \sum_{j,k}\overline{c_j}\, c_k\, M_{jk} = c^{*} M c,$$

which is $\ge 0$ for all $c$ **iff** the OS3 matrix $M$ of (RP) is PSD. So:

> **OS3 ($M$ is PSD) $\iff$ the reflected form $(\cdot,\cdot)_{\mathrm{phys}}$ is positive
> semidefinite on $\mathcal{E}_+$.**

### 5.3 GNS quotient-and-complete

A positive *semi*definite form is one step short of an inner product: it can have a null
space $\mathcal{N} = \{F : (F, F)_{\mathrm{phys}} = 0\}$. The Gelfand–Naimark–Segal
construction quotients it out and completes,

$$\mathcal{H}_{\mathrm{phys}} = \overline{\,\mathcal{E}_+ \big/ \mathcal{N}\,}^{\;(\cdot,\cdot)_{\mathrm{phys}}}.$$

OS3 guarantees the quotient form is strictly positive, so the completion is a genuine Hilbert
space with a *positive* norm. Without OS3 one gets negative-norm states ("ghosts") and no
probability interpretation. Downstream, each reconstruction step *uses* positivity:

- **Hamiltonian.** Euclidean-time translation by $t > 0$ maps $\mathcal{E}_+$ into itself and
  descends to a contraction semigroup $e^{-tH}$ with $H \ge 0$ — a positive energy spectrum;
  $\lVert e^{-tH}\rVert \le 1$ is the operator shadow of the same inequality.
- **Wick rotation.** Because $H \ge 0$, the semigroup $e^{-tH}$ continues $t \mapsto it$ to a
  *unitary* group $e^{-itH}$ — Euclidean correlations continue to Minkowski ones.
- **Vacuum.** The constant functional $\mathbf{1} \in \mathcal{E}_+$ becomes the cyclic vacuum
  $\Omega$, with $H\Omega = 0$.

$$\text{OS3 (RP)} \Longrightarrow (\cdot,\cdot)_{\mathrm{phys}} \ge 0
\Longrightarrow \mathcal{H}_{\mathrm{phys}}\text{ with positive norm}
\Longrightarrow H \ge 0,\ \text{unitary } e^{-itH},\ \Omega.$$

### 5.4 The zero-norm vectors for the GFF

For the *free* field the null space is explicit. From the mixed representation (RP-cov) of
Section 3,

$$R(f, f) = \int \frac{d\bar k}{2\,\omega_{\bar k}}\,\big\lvert F_{\omega}(-\bar k)\big\rvert^2,
\qquad F_\omega(\bar k) = \int_0^\infty e^{-\omega t}\,\hat f(t, \bar k)\, dt,$$

so a positive-time $f$ is null exactly when its **mass-shell time-Laplace transform vanishes**,
$F_\omega(\bar k) = 0$ for a.e. $\bar k$. The equation-of-motion directions
$f = (-\Delta + m^2)\, g$ with $g \in C_c^\infty(\{x_0 > 0\})$ land in this kernel —
integrating by parts, the boundary terms vanish because $g$ is flat at $t = 0$. Physically:
smearing the field against $(-\Delta + m^2)g$ gives a zero-norm state because that combination
vanishes *on shell*. The quotient map $f \mapsto F_\omega$ sends the one-particle sector onto
(a dense subspace of) the relativistic one-particle space
$L^2\!\big(\mathbb{R}^{d-1}, \tfrac{d\bar k}{2\omega_{\bar k}}\big)$ — wavefunctions of spatial
momentum with the Lorentz-invariant measure.

### 5.5 How the two proof layers map onto the physics

- **`OS3_CovarianceRP`** ($R$ PSD) is positivity of the **one-particle** structure — the
  reflected propagator is a positive kernel, with radical the EOM directions of §5.4.
- **`OS3_ReflectionPositivity`** (Schur–Hadamard: $e^{\circ R}$ PSD $\Rightarrow M$ PSD) is the
  **second quantization** to Fock space
  $\mathcal{H}_{\mathrm{phys}} = \Gamma\big(\overline{\mathcal{E}_+^{(1)}/\mathcal{N}_1}\big)$:
  the entrywise exponential *is* the passage from the one-particle inner product to the Fock
  inner product, carrying the one-particle radical to the full null space.

That is the precise sense in which OS3 *is* Hilbert-space positivity: it is the
necessary-and-sufficient Euclidean condition for the reconstructed quantum theory to have a
positive-definite inner product — equivalently, a Hamiltonian with non-negative spectrum.

---

## Dimension note: why there is no upper bound on $d$

Every OS axiom — and the Minlos measure construction, Plancherel, positive-definiteness, and
the covariance's decay and integrability — is **uniform in $d \ge 2$** (see
[`../dimension_generic.md`](../dimension_generic.md)). The lower bound $2 \le d$ is intrinsic
and permanent: reflection positivity reflects a *time* coordinate, which needs a time axis
and the $\mathbb{R} \times \mathbb{R}^{d-1}$ split. The delicate point is OS3's proper-time /
spatial-momentum Fubini exchange
([`fubini_s_ksp_swap`](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L2650)), which requires an
$s$-integrable dominator near $s = 0$
([`integrable_dominate_G`](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L858)).

**Why order-$d$ vanishing.** A positive-time Schwartz function is flat to *all* orders at
$\{x_0 = 0\}$: its time derivative is again a Schwartz function vanishing on the half-space,
so induction gives, for every $N$, a bound $\lVert f(x)\rVert \le C_N\, x_0^N$
([`schwartz_vanishing_pow_bound`](../../OSforGFF/Spacetime/ProdIntegrable.lean)). Feeding the
order-$N$ bound through the time-Gaussian moment produces the dominator
$\sim s^{\,N + 1/2}\, e^{-s(\lVert \bar k\rVert^2 + m^2)}$ (the heat-kernel prefactor
$(4\pi s)^{-d/2}$ cancels the spatial Fourier volume $(4\pi s)^{(d-1)/2}$, leaving the 1-D
factor $(4\pi s)^{-1/2}$, and each order of vanishing contributes one power of $s$).
Integrating the momentum over $\mathbb{R}^{d-1}$ leaves the outer $s$-integrand

$$\sim s^{\,N + 1 - d/2}\, e^{-s m^2}, \qquad \text{integrable near } s = 0 \iff N > \tfrac{d}{2} - 2,$$

so taking $N = d$ works in every dimension. (First-order vanishing, $N = 1$, gives the sharp
constraint $d \le 5$ — the historical form of the library, whose $N = 1$ lemmas survive as
corollaries.) The Schur–Hadamard lift of Section 4 is entirely dimension-free. The history of
the $d \le 5$ bound and its removal is recorded in
[`../general_dimension.md`](../general_dimension.md).

> **One line:** $2 \le d$ is structural and permanent; the upper bound is gone — order-$d$
> boundary vanishing keeps the OS3 domination integrable in every dimension.

---

## One-paragraph summary

OS3 is proved by a four-stage pipeline, uniform in $d \ge 2$. `OS3_MixedRepInfra`
establishes that the relevant heat-kernel integrals converge and may be interchanged,
replacing the non-integrable naive Fourier kernel by the proper-time (Schwinger)
representation. `OS3_MixedRep` uses that to rewrite the reflected two-point form
$\langle \theta f, C f\rangle$ as a **spatial Fourier integral whose time kernel is a pure
exponential** $\tfrac{1}{2\omega}\, e^{-\omega\lvert x_0 + y_0\rvert}$,
$\omega = \sqrt{\lVert \bar k\rVert^2 + m^2}$. `OS3_CovarianceRP` restricts to positive time
so that exponential **factorizes** $e^{-\omega(x_0 + y_0)} = e^{-\omega x_0}\, e^{-\omega y_0}$,
making $\langle \theta f, C f\rangle$ a sum of squared moduli — covariance reflection
positivity. Finally `OS3_ReflectionPositivity` lifts this scalar inequality to the full
generating-functional matrix (RP) via the **Schur–Hadamard argument**: for a Gaussian field
each matrix entry is an entrywise exponential $e^{R_{jk}}$ of the (PSD) reflected covariance
$R$, and the entrywise exponential of a PSD matrix is PSD because it is a non-negative series
of Hadamard powers, each PSD by the Schur product theorem. By Osterwalder–Schrader
reconstruction (Section 5) this positivity is exactly what makes the reflected form
$(\cdot,\cdot)_{\mathrm{phys}}$ a positive-definite inner product — yielding the physical Fock
space, a Hamiltonian $H \ge 0$, and Wick rotation to real time. OS3 is thus both the *deepest*
axiom (two real ideas — the mixed representation and entrywise-exponential positivity) and the
*longest* (a large technical Fubini layer beneath them). Its only dimension restriction is the
structural $d \ge 2$; the Fubini dominator runs at boundary-vanishing order $d$, so no upper
bound is needed.

---

## Pointers into the code

Optional — for when you open the Lean. Every visible `:NNN` label matches its `#LNNN` anchor.

| Result | File | Name |
|---|---|---|
| Heat-kernel / Schwinger rep of the propagator | [OS/OS3_MixedRepInfra.lean:186](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L186) | `heatKernel_eq_gaussianFT` |
| Fubini domination (order-$d$ dominator) | [OS/OS3_MixedRepInfra.lean:858](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L858) | `integrable_dominate_G` |
| Proper-time / spatial-momentum swap | [OS/OS3_MixedRepInfra.lean:2650](../../OSforGFF/OS/OS3_MixedRepInfra.lean#L2650) | `fubini_s_ksp_swap` |
| Mixed representation (MR) | [OS/OS3_MixedRep.lean:1467](../../OSforGFF/OS/OS3_MixedRep.lean#L1467) | `bessel_bilinear_eq_mixed_representation` |
| Covariance reflection positivity (complex) | [OS/OS3_CovarianceRP.lean:412](../../OSforGFF/OS/OS3_CovarianceRP.lean#L412) | `freeCovariance_reflection_positive_bilinear` |
| Covariance reflection positivity (real) | [OS/OS3_CovarianceRP.lean:463](../../OSforGFF/OS/OS3_CovarianceRP.lean#L463) | `freeCovariance_reflection_positive_real` |
| Reflected covariance matrix is PSD | [OS/OS3_ReflectionPositivity.lean:93](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L93) | `freeCovarianceFormR_reflection_matrix_posSemidef` |
| Schur product (complex Hadamard) | [OS/OS3_ReflectionPositivity.lean:707](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L707) | `posSemidef_hadamard_complex` |
| Entrywise $\exp$ of PSD is PSD (complex) | [OS/OS3_ReflectionPositivity.lean:724](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L724) | `entrywiseExp_IsRePSD` |
| OS3 for the GFF (real) | [OS/OS3_ReflectionPositivity.lean:500](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L500) | `gaussianFreeField_OS3_real` |
| OS3 for the GFF (complex / star) | [OS/OS3_ReflectionPositivity.lean:989](../../OSforGFF/OS/OS3_ReflectionPositivity.lean#L989) | `QFT.gaussianFreeField_OS3` |
| OS3 predicate | [OS/Axioms.lean:112](../../OSforGFF/OS/Axioms.lean#L112) | `OS3_ReflectionPositivity` |
| Master theorem (generic) | [OS/Master.lean:61](../../OSforGFF/OS/Master.lean#L61) | `gaussianFreeField_satisfies_all_OS_axioms_generic` |

Auto-generated theorem inventories:
[`OS3_MixedRepInfra.md`](../../summary/OSforGFF/OS/OS3_MixedRepInfra.md),
[`OS3_MixedRep.md`](../../summary/OSforGFF/OS/OS3_MixedRep.md),
[`OS3_CovarianceRP.md`](../../summary/OSforGFF/OS/OS3_CovarianceRP.md),
[`OS3_ReflectionPositivity.md`](../../summary/OSforGFF/OS/OS3_ReflectionPositivity.md).
Architecture and the dimension story:
[`../architecture.md`](../architecture.md),
[`../dimension_generic.md`](../dimension_generic.md),
[`../general_dimension.md`](../general_dimension.md).

---

*Companions: [Overview.md](Overview.md), [OS0.md](OS0.md), [OS1OS2.md](OS1OS2.md), [OS4.md](OS4.md).*
