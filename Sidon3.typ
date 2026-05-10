#import "@preview/arkheion:0.1.2": *

#show: arkheion.with(
  title: "The exact Sidon constant of {0, 1, 2, 3} and its formalization",
  authors: (
    (name: "Haoxiang Yu", email: "yhx12243@gmail.com", affiliation: ""),
    (name: "Deepseek", email: "noreply@deepseek.com", affiliation: ""),
    (name: "Claude Code", email: "noreply@anthropic.com", affiliation: ""),
  ),
  abstract: text(0.833333em, [
    We determine the exact value of the Sidon constant of the four-element set
    ${0,1,2,3}$ to be $5/3$. The lower bound was established by Neuwirth via
    an explicit family of trigonometric polynomials; we prove the matching upper
    bound. Our proof introduces a new method: given a point on the unit circle we
    construct a cubic self-inversive polynomial whose three roots lie on the unit
    circle, extract positive real weights from these roots, and use a weighted
    square-sum identity to obtain the sharp estimate. The entire proof is
    formalized in Lean~4 using mathlib.
  ]),
  keywords: ("Sidon constant", "Analysis", "Functional Analysis", "Formalization", "Lean 4"),
  date: datetime.today().display("[month repr:long] [day], [year]"),
)

= Introduction

A set of integers $Λ subset ZZ$ is called a *Sidon set* if there exists
a constant $C$ such that for every trigonometric polynomial with spectrum in
$Λ$,
$
  ∑_(Λ in Λ) abs(c_Λ)
  ≤ C thin
  norm(∑_(Λ in Λ) c_Λ e^(i Λ t))_∞,
$
where $norm(f)_∞ = max_(t in 𝕋) abs(f(t))$ and
$𝕋 = {z in ℂ : abs(z) = 1}$ is the unit circle.
The optimal constant $S(Λ)$ is the *Sidon constant* of $Λ$.
Equivalently, $S(Λ)$ is the supremum of $sum abs(c_Λ)$ over all
trigonometric polynomials with spectrum in $Λ$ bounded by $1$ in supremum
norm. Equivalently again, $S(Λ)$ is the complex unconditionality constant
of the sequence of characters ${e^(i Λ t)}_(Λ in Λ)$ in the
space $C(𝕋)$ of continuous functions on the unit circle.

For the initial segment $Λ = {0,1,dots,N}$, Newman (see
@shapiro1951extremal) obtained the upper bound $S(Λ) ≤ sqrt(N)$ via an
averaging argument over the $N$-th roots of unity, improving the trivial
bound $sqrt(N+1)$ from Parseval's theorem. Shapiro proved that equality
$S(Λ) = sqrt(N)$ can hold exactly when $N in {1,2,4}$. In particular,
$S({0,1,2,3}) < √3 approx 1.732$, but the exact value was not
determined.

For three-element sets, Neuwirth @neuwirth2001sidonconstantsetselements
completely solved the problem, proving that
$
  S({Λ_0, Λ_1, Λ_2})
  = sec(frac(pi, 2n)),
  quad
  n = frac(max abs(Λ_i - Λ_j), "gcd"(Λ_1 - Λ_0, Λ_2 - Λ_0)).
$
This yields $S({0,1,2}) = √2$ and $S({0,1,3}) = 2 / √3$, but
${0,1,2,3}$ is a set of four elements and does not fit this framework. In
that same paper, Neuwirth conjectured $S({0,1,2,3}) = 5/3$.

The lower bound $5/3 ≤ S({0,1,2,3})$ was established by Neuwirth
@neuwirth2026fourieranalyticsidonconstant twenty-five years later, together
with a proof that the *real* unconditional constant of ${0,1,2,3}$ is
exactly $5/3$ and the general upper bound $S(Λ) ≤ sqrt(abs(Λ)-1)$
for all finite $Λ$. The sharp upper bound for the complex Sidon constant,
however, remained open.

In this paper we prove the upper bound $S({0,1,2,3}) ≤ 5/3$, thereby
establishing:

*Main Theorem*. $S({0,1,2,3}) = 5/3$.

Our proof introduces a method that may be of independent interest. Given a
unimodular parameter $ξ$ (which encodes the relative phase between the
extremal coefficients $a_0$ and $a_3$), we construct the cubic polynomial
$
  P(X) = X^3 - psi X^2 + psi X - ξ,
  quad
  psi = frac(ξ + 1, 4).
$
We prove that $P$ is *self-inversive* and that its three roots $z_1, z_2, z_3$
all lie on the unit circle. From these roots we extract positive real weights
$
  μ_j = frac(18, 6 - 2*Re(z_j) + Re(z_j^2)) > 0
$
satisfying four remarkable moment identities:
$
  ∑_(j=1)^3 μ_j = 10, quad
  ∑_(j=1)^3 μ_j z_j = 2, quad
  ∑_(j=1)^3 μ_j z_j^2 = -2, quad
  ∑_(j=1)^3 μ_j z_j^3 = -1 + 9 ξ^*.
$
A weighted square-sum identity then yields, for any polynomial
$f(z) = a_0 + a_1 z + a_2 z^2 + a_3 z^3$ bounded by $1$,
$
  6 norm(a_1 + a_2)^2 + 9 norm(ξ a_0 + a_3)^2 ≤ 10.
$
Together with a reduction step that aligns coefficients and a binary
Cauchy--Schwarz estimate, this gives the sharp bound $sum norm(a_j) ≤ 5/3$.

The entire proof of the upper bound has been formalized in Lean~4 using
mathlib. We discuss the formalization in Section~5.

The paper is organized as follows. Section~2 reviews related work.
Section~3 collects preliminaries on self-inversive polynomials.
Section~4 contains the complete proof, broken into subsections tracing the
logical arc described above. Section~5 discusses the formalization.
Section~6 lists open questions.

= Related Works

== The three-element case

Neuwirth @neuwirth2001sidonconstantsetselements solved the extremal problem
for sets of three frequencies. By reducing to a real-variable optimization in
two parameters and analyzing the critical points of
$Phi(t, theta.alt) = abs(1 + r e^(i theta.alt) e^(i k t) + s e^(i l t))^2$, he
proved that the minimum of $max_t Phi(t, theta.alt)$ over phases $theta.alt$
oℂurs at $theta.alt = pi/l$ (where $k, l$ are the normalized frequency
differences). This yields the exact formula
$
  S({Λ_0, Λ_1, Λ_2})
  = sec(frac(pi, 2n)),
$
with $n = max abs(Λ_i - Λ_j) / "gcd"(Λ_1 - Λ_0, Λ_2 -
Λ_0)$. In particular, $S({0,1,2}) = √2$ (recovering Newman's
result) and $S({0,1,3}) = 2/√3$. The extremal polynomials have
coefficients proportional to the frequency gaps and carry sign patterns
determined by the 2-adic valuations of the differences. An important
consequence is that for three-element sets, the real and complex
unconditionality constants coincide in $C(𝕋)$. The paper concludes by
conjecturing $S({0,1,2,3}) = 5/3$.

== Lower bound and earlier upper bounds

Neuwirth @neuwirth2026fourieranalyticsidonconstant established the lower bound
$S({0,1,2,3}) ≥ 5/3$ by exhibiting a one-parameter family of trigonometric
polynomials
$
  f_tau (z) = frac(i 2 √2 cos tau - 1 - 3 sin tau, 15)
  + frac(3 + sin tau, 10) z
  + frac(3 - sin tau, 10) z^2
  + frac(i 2 √2 cos tau - 1 + 3 sin tau, 15) z^3
$
whose coefficients satisfy $sum abs(c_j) = 1$ for every $tau$ and whose
supremum norm is identically $3/5$ on the unit circle. The calculation
involves solving the critical point equations of
$Phi(t,tau) = abs(f(e^(i t),tau))^2$; for each $tau$ there are exactly three
points on the circle attaining the maximum $9/25$, and a careful algebraic
elimination yields the parameterization.

The same paper also gave an independent proof of the general bound
$S(Λ) ≤ sqrt(abs(Λ)-1)$ by interpreting the Sidon constant as the
norm of linear functionals on $C_Λ(𝕋)$ and lifting them to sums of Dirac
measures on roots of unity. For $Λ = {0,1,2,3}$ this gives
$S(Λ) ≤ √3$, which is not sharp. Finally, the real unconditional
constant of ${0,1,2,3}$ was shown to be exactly $5/3$ by explicitly
evaluating all sign patterns modulo symmetries.

What remained open was the sharp upper bound for the complex Sidon constant.
Our main contribution is closing this gap.

= Preliminaries

We work over the complex numbers. The unit circle is
$𝕋 = {z in ℂ : abs(z) = 1}$ and the closed unit disk is
$𝔻 = {z in ℂ : abs(z) ≤ 1}$. For $z in 𝕋$ we write $z^* = z^(-1)$.
$ℂ[X]$ denotes polynomials in one variable with complex coefficients.

== Sidon constant and linear functionals

For a finite set $Λ subset ZZ$, let $C_Λ (𝕋)$ be the subspace of
$C(𝕋)$ spanned by the characters ${e_Λ : z ↦ z^Λ}_(
Λ in Λ)$. A linear functional $ell$ on $C_Λ (𝕋)$ is determined
by its values $u_Λ = ell(e_Λ)$. By the Hahn--Banach and Riesz
representation theorems, the norm of $ell$ satisfies
$
  norm(ell) = inf{
    sum abs(b_k) : ell(f) = sum b_k f(z_k),
    ∀ f in C_Λ(𝕋)
  },
$
where the $z_k$ are points on $𝕋$. The Sidon constant admits the dual
characterization
$
  S(Λ) = sup{
    norm(ell) : abs(ell(e_Λ)) = 1,
    ∀ Λ in Λ
  }.
$

== Self-inversive polynomials

*Definition* (Self-inversive polynomial).
  A polynomial $P in ℂ[X]$ of degree $n$ is *self-inversive* if
  $ P(0)^* thin X^n thin P(1/X^*)^* = "lc"(P)^* thin P(X), $
  where $"lc"(P)$ is the leading coefficient. Equivalently, for all
  $0 ≤ i ≤ n$,
  $ "lc"(P)^* dot.op "coeff"_i (P) = "coeff"_(n-i)(P)^* dot.op P(0). $

Self-inversive polynomials generalize self-reciprocal (palindromic)
polynomials and characterize those whose roots are symmetric with respect to
the unit circle: if $r$ is a root with multiplicity $m$, then $1/r^*$ is
also a root with the same multiplicity. An immediate consequence:

*Lemma* (Leading coefficient and constant term).
  If $P$ is self-inversive and $P(0) != 0$, then
  $norm("lc"(P)) = norm(P(0))$.

*Lemma* (Disk to sphere).
  If $P$ is self-inversive and all its roots lie in the closed unit disk
  $𝔻$, then all its roots lie on the unit circle $𝕋$.

_Proof_:
  Let $r$ be a root. By self-inversivity, $1/r^*$ is also a root.
  If $abs(r) < 1$ then $abs(1/r^*) > 1$, contradicting the assumption
  that all roots lie in $𝔻$. The case $abs(r) > 1$ is excluded by
  hypothesis. Thus $abs(r) = 1$.

== Gauss--Lucas theorem

We rely on the following classical result:

*Theorem* (Gauss--Lucas).
  The roots of the derivative $P'$ of a polynomial $P$ lie in the convex hull
  of the roots of $P$.

In particular, if all roots of $P$ lie in $𝔻$, then all roots of
$P'$ lie in $𝔻$ as well, since $𝔻$ is convex.

== Cohn's root theorem about self-inversive polynomials

The following lemma controls the modulus of a self-inversive polynomial's
reversal outside the disk. It is a special case of the Cohn's root theorem@cohn1922anzahl about self-inversive polynomials.

*Lemma* (Blaschke product estimate).
  Let $P in ℂ[X]$ have all its roots in $𝔻$. Then for any
  $r in ℂ$ with $abs(r) ≥ 1$,
  $ abs(P_"rev" (r)) ≤ abs(P(r)), $
  where $P_"rev" (X) = X^(deg P) thin P(1/X^*)^*$.

_Proof_:
  Factor $P$ over its roots $r_k$: $P(X) = c ∏ (X - r_k)$. Then
  $P_"rev" (X) = c^* ∏ (1 - r_k^* X)$.
  Evaluating at $r$ and comparing moduli, each factor satisfies
  $abs(r - r_k)^2 - abs(1 - r_k^* r)^2
  = (abs(r)^2 - 1)(1 - abs(r_k)^2) ≥ 0$
  since $abs(r_k) ≤ 1$ and $abs(r) ≥ 1$. Hence
  $abs(1 - r_k^* r) ≤ abs(r - r_k)$ and the product inequality follows.

*Theorem* (Cohn).
  Let $P in ℂ[X]$ be a self-inversive polynomial. Then all roots of $P$ lie on
  the unit circle $𝕋$ if and only if all roots of the derivative $P'$ lie in
  the closed unit disk $𝔻$.

_Proof_.  ($⇒$) If all roots of $P$ lie on $𝕋 subset 𝔻$, then
by Gauss--Lucas the roots of $P'$ lie in the convex hull of the roots of $P$,
which is contained in $𝔻$.

($⇐$) Suppose all roots of $P'$
lie in $𝔻$.  Let $alpha = "lc"(P)$, $beta = P(0)$, and
$n = deg P$.  Self-inversivity yields the polynomial identity
$
  alpha^* dot (X P'(X)) + beta dot P'_"rev" (X) = n alpha^* P(X).
$
Evaluating at any root $r$ of $P$, we obtain
$abs(r P'(r)) = abs(P'_"rev" (r))$.
If $abs(r) > 1$, the Blaschke estimate applied to $P'$ gives
$abs(P'_"rev" (r)) <= abs(P'(r))$, hence
$abs(r) abs(P'(r)) <= abs(P'(r))$, forcing $abs(r) <= 1$, a contradiction.
Thus all roots lie in $𝔻$, and by the disk-to-sphere lemma they must
lie on $𝕋$. □

= Solution

In this section we prove the main theorem. Let
$ f(z) = a_0 + a_1 z + a_2 z^2 + a_3 z^3, quad a_j in ℂ. $
Assume $norm(f)_∞ ≤ 1$, i.e., $abs(f(z)) ≤ 1$ for all $z in 𝕋$.
Our goal is to show $∑_(j=0)^3 norm(a_j) ≤ 5/3$.

== Reduction to aligned coefficients

We first simplify the configuration of the coefficients through two
normalization steps.

*Lemma* (Alignment of $a_1$, $a_2$).
  Without loss of generality, we may assume
  $norm(a_1) + norm(a_2) = norm(a_1 + a_2)$.

_Proof_:
  If $a_1 = 0$ or $a_2 = 0$ the equality is trivial. Otherwise, set
  $mu = "normalize"(a_1/a_2)$ (the unimodular complex number with the same
  argument as $a_1/a_2$). Because $abs(mu) = 1$, the rotated polynomial
  $f(mu z)$ still satisfies $norm(f(mu dot.c))_∞ ≤ 1$, and its
  coefficients become $(mu a_1, mu^2 a_2)$ which are positively aligned:
  $norm(mu a_1) + norm(mu^2 a_2) = norm(mu a_1 + mu^2 a_2)$. The sum of
  coefficient moduli is unchanged. Hence we may work with the rotated
  polynomial.

With $a_1, a_2$ aligned, we have
$
  norm(a_0) + norm(a_1) + norm(a_2) + norm(a_3)
  = norm(a_0) + norm(a_1 + a_2) + norm(a_3).
$

*Lemma* (Alignment of $a_0$, $a_3$).
  There exists $ξ in 𝕋$ such that
  $norm(a_0) + norm(a_3) = norm(ξ a_0 + a_3)$.

_Proof_:
  This is a general fact: for any two complex numbers $a, b$ with $b != 0$,
  the function $g(z) = norm(z a + b) - norm(a)$, defined for unimodular $z$,
  attains its maximum value $norm(b)$ at some $ξ in 𝕋$. (Take
  $ξ = "normalize"(b/a)$ when $a != 0$; otherwise any $ξ$ works.)

Applying both lemmas, we may assume
$
  norm(a_1) + norm(a_2) = norm(a_1 + a_2), quad
  norm(a_0) + norm(a_3) = norm(ξ a_0 + a_3)
$
for some fixed $ξ$ with $abs(ξ) = 1$.

We now apply a binary Cauchy--Schwarz estimate. Write
$
  S = norm(a_0) + norm(a_1 + a_2) + norm(a_3)
$
and set $r_1 = norm(a_1 + a_2)$, $r_2 = norm(ξ a_0 + a_3)$. Since
$norm(a_0) + norm(a_3) = r_2$, the total sum is $S = r_1 + r_2$.
The elementary inequality
$(r_1 + r_2)^2 ≤ (f_1 + f_2)(r_1^2/f_1 + r_2^2/f_2)$ (a Cauchy--Schwarz
inequality on a discrete two-point space, with $f_1 = 6$, $f_2 = 9$) gives:
$
  S^2 ≤ (6 + 9) (norm(a_1 + a_2)^2/6 + norm(ξ a_0 + a_3)^2/9)
  = 15 dot.op frac(6 norm(a_1 + a_2)^2 + 9 norm(ξ a_0 + a_3)^2, 18).
$
Thus,
$
  (∑_(j=0)^3 norm(a_j))^2
  ≤ (6^(-1) + 9^(-1))
     ( 6 norm(a_1 + a_2)^2 + 9 norm(ξ a_0 + a_3)^2 ).
$

The problem is reduced to proving
$6 norm(a_1 + a_2)^2 + 9 norm(ξ a_0 + a_3)^2 ≤ 10$, which will yield
$S^2 ≤ frac(5,18) dot.op 10 = frac(25,9)$, hence $S ≤ 5/3$.

== The key polynomial system

Fix $ξ in 𝕋$ from the previous section. Define
$
  psi = frac(ξ + 1, 4), quad
  P(X) = X^3 - psi X^2 + psi X - ξ.
$

*Lemma* (Basic properties of $P$).
  $P$ is a monic self-inversive polynomial of degree $3$.

_Proof_:
  Monicity and degree are clear from the definition. For self-inversivity,
  write $P(X) = X^3 + c_2 X^2 + c_1 X + c_0$ with $c_2 = -psi$,
  $c_1 = psi$, $c_0 = -ξ$. With $c_3 = 1$, the coefficient condition
  reads $c^*_0 c_i = c^*_(3-i) c_3$ for $i = 0, 1, 2, 3$.
  The key relation is $psi^* ξ = psi$, which follows from
  $ psi^* ξ = frac(ξ^* + 1, 4) ξ = frac(1 + ξ, 4) = psi, $
  using $abs(ξ) = 1$. The other verifications are straightforward.

*Lemma* (Roots of $Q$ lie in the open unit disk).
  Let $Q(X) = P'(X) = 3X^2 - 2 psi X + psi$. Every root $r$ of $Q$ satisfies
  $abs(r) < 1$.

_Proof_:
  From $Q(r) = 0$ we have $(2r - 1) psi = 3r^2$.
  Taking moduli, $3 abs(r)^2 = abs(2r - 1) dot.op abs(psi)$.
  Since $abs(ξ) = 1$, the triangle inequality gives
  $
    abs(psi) = frac(abs(ξ + 1), 4) ≤ frac(2, 4) = 1/2.
  $
  Thus
  $3 abs(r)^2 ≤ 1/2 dot.op abs(2r - 1)
  ≤ 1/2 (2 abs(r) + 1) = abs(r) + 1/2$.
  The inequality $3 x^2 ≤ x + 1/2$ implies $x < 1$, since
  $3x^2 - x - 1/2 = 0$ has largest root $(1 + sqrt(7))/6 approx 0.607 < 1$.

*Theorem* (Roots of $P$ lie on the unit circle).
  All three roots $z_1, z_2, z_3$ of $P$ satisfy $abs(z_j) = 1$, and they
  are pairwise distinct.

_Proof_:
  The previous lemma shows that $Q = P'$ has all its roots in the open unit
  disk $"int"(𝔻)$. In particular, all roots of $Q$ lie in the closed unit disk
  $𝔻$. Since $P$ is self-inversive, Cohn's theorem (Section~3)
  immediately yields that all roots of $P$ lie on the unit circle $𝕋$:
  $abs(z_j) = 1$ for $j = 1, 2, 3$.

  Since all roots of $P$ lie on the unit circle while all roots of $P'$ lie in the open unit disk, $P$ and $P'$ must be coprime, which implies the separability of $P$. Moreover, $z_1, z_2, z_3$ are pairwise distinct.

From Vieta's formulas applied to $P(X) = (X - z_1)(X - z_2)(X - z_3)$,
we immediately obtain the symmetric sum relations:

*Proposition* (Root relations):
  The roots $z_1, z_2, z_3$ of $P$ satisfy
  $
    z_1 + z_2 + z_3 = psi, quad
    z_1 z_2 + z_1 z_3 + z_2 z_3 = psi, quad
    z_1 z_2 z_3 = ξ.
  $
  In particular, $abs(z_j) = 1$ for $j = 1, 2, 3$.

== The $Λ$ coefficients and moment identities

We now define a rational function $Λ$ of three variables that, when
evaluated at the roots of $P$, produces positive real weights.

*Definition* ($Λ$ coefficients).
  For distinct complex numbers $z_1, z_2, z_3$, define
  $
    Λ(z_1, z_2, z_3)
    = frac(2(5 z_2 z_3 - z_2 - z_3 - 1), (z_1 - z_2)(z_1 - z_3)).
  $
  Set $μ_1 = Λ(z_1, z_2, z_3)$,
  $μ_2 = Λ(z_2, z_3, z_1)$,
  $μ_3 = Λ(z_3, z_1, z_2)$,
  obtained by cyclic permutation.

*Theorem* (Moment identities).
  The weights $μ_1, μ_2, μ_3$ satisfy:
  $ μ_1 + μ_2 + μ_3 &= 10, \
  μ_1 z_1 + μ_2 z_2 + μ_3 z_3 &= 2, \
  μ_1 z_1^2 + μ_2 z_2^2 + μ_3 z_3^2 &= -2, \
  μ_1 z_1^3 + μ_2 z_2^3 + μ_3 z_3^3 &= -1 + 9 ξ. $

_Proof_:
  These identities are verified by rational function algebra. The
  denominators $(z_1 - z_2)(z_1 - z_3)$ are nonzero because the $z_j$ are
  pairwise distinct. Clearing denominators, each identity reduces to a
  polynomial relation among $z_1, z_2, z_3$ that follows from the root
  relations $z_1+z_2+z_3 = psi$, $z_1 z_2+z_1 z_3+z_2 z_3 = psi$,
  $z_1 z_2 z_3 = ξ$, together with $psi = (ξ+1)/4$.
  The computations are elementary though lengthy; the Lean formalization
  carries them out using the `field` tactic for rational simplifications.

  As an illustration, for the cubic moment (5), we use
  $z_j^3 = psi z_j^2 - psi z_j + ξ$ (since $P(z_j) = 0$) together with
  moments (2)--(4) and $psi = (ξ+1)/4$:
  $
    sum μ_j z_j^3 &= psi sum μ_j z_j^2 - psi sum μ_j z_j + ξ sum μ_j \
    &= psi(-2) - psi(2) + ξ(10) \
    &= -4 psi + 10 ξ \
    &= -4 frac(ξ+1, 4) + 10 ξ \
    &= -1 + 9 ξ.
  $

The second crucial fact is that these weights are positive reals.

*Lemma* (Positivity of the weights).
  When $abs(z_1) = abs(z_2) = abs(z_3) = 1$, the weight
  $μ_1 = Λ(z_1, z_2, z_3)$ depends only on $z_1$ and simplifies to a
  positive real number:
  $
    Λ(z_1, z_2, z_3)
    = frac(36 z_1^2, 1 - 2z_1 + 12z_1^2 - 2z_1^3 + z_1^4)
    = frac(18, 6 - 2 Re(z_1) + Re(z_1^2)) > 0.
  $
  In particular, $μ_1, μ_2, μ_3$ are all positive real numbers.

_Proof_:
  Using the root relations and $P(z_1) = 0$, express $psi$ and the
  symmetric sums of $z_2, z_3$ in terms of $z_1$. Concretely,
  $z_2 + z_3 = psi - z_1$ and
  $z_2 z_3 = psi - z_1(z_2 + z_3)
  = psi - z_1(psi - z_1) = z_1^2 - psi z_1 + psi$.
  Using $P(z_1) = 0$ to eliminate $psi$, the rational expression simplifies
  to the stated form.

  For $abs(z) = 1$, we use $z^(-1) = z^*$ to rewrite the denominator:
  $
    1 - 2z + 12z^2 - 2z^3 + z^4
    &= z^2(z^(-2) - 2z^(-1) + 12 - 2z + z^2) \
    &= z^2(z^*^2 - 2 z^* + 12 - 2z + z^2) \
    &= z^2(12 - 4 Re(z) + 2 Re(z^2)).
  $
  Thus $Λ' = 36 z^2 / (z^2(12 - 4 Re(z) + 2 Re(z^2)))
  = 18 / (6 - 2 Re(z) + Re(z^2))$.

  The denominator is strictly positive because for $abs(z) ≤ 1$,
  $6 - 2 Re(z) + Re(z^2) ≥ 6 - 2 - 1 = 3 > 0$.

== The weighted square-sum identity

Consider $f(z) = a_0 + a_1 z + a_2 z^2 + a_3 z^3$. For any $z in 𝕋$, the
modulus squared expands as a Hermitian form:
$
  abs(f(z))^2
  = (∑_(j=0)^3 a_j z^j)
    (∑_(k=0)^3 a^*_k z^*^k)
  = ∑_(j,k=0)^3 a_j a^*_k , z^(j-k).
$
Using $z^* = z^(-1)$ on $𝕋$, we can write this as a Laurent polynomial
whose real part is a trigonometric polynomial in the argument of $z$.
Concretely,
$
  abs(f(z))^2 = Re(
    ∑_(j=0)^3 abs(a_j)^2
    + 2(a^*_0 a_1 + a^*_1 a_2 + a^*_2 a_3) z
    + 2(a^*_0 a_2 + a^*_1 a_3) z^2
    + 2 a^*_0 a_3 z^3
  ).
$

Now evaluate this expression at $z_1, z_2, z_3$, multiply by the positive
weights $μ_1, μ_2, μ_3$, and sum.

*Theorem* (Weighted square-sum identity).
  $
    ∑_(j=1)^3 μ_j thin abs(f(z_j))^2
    = abs(a_0 + 2a_1 - 2a_2 - a_3)^2
    + 6 abs(a_1 + a_2)^2
    + 9 abs(ξ^* a_0 + a_3)^2.
  $

_Proof_:
  Writing
  $delta_0 = sum abs(a_j)^2$,
  $delta_1 = a^*_0 a_1 + a^*_1 a_2 + a^*_2 a_3$,
  $delta_2 = a^*_0 a_2 + a^*_1 a_3$,
  $delta_3 = a^*_0 a_3$,
  we have
  $
    abs(f(z_j))^2 = Re(delta_0
      + 2 delta_1 z_j
      + 2 delta_2 z_j^2
      + 2 delta_3 z_j^3).
  $
  Since $μ_j$ are real, the weighted sum is
  $
    ∑_(j=1)^3 μ_j abs(f(z_j))^2
    = Re(
      delta_0 sum μ_j
      + 2 delta_1 sum μ_j z_j
      + 2 delta_2 sum μ_j z_j^2
      + 2 delta_3 sum μ_j z_j^3
    ).
  $
  Substituting the four moment identities (2)--(5) replaces each sum by its
  known value, and expanding the real part yields exactly the sum-of-squares
  expression stated. The computation, while lengthy, is a purely algebraic
  verification.

== The core inequality

Since $norm(f)_∞ ≤ 1$, we have $abs(f(z_j)) ≤ 1$ for each root
$z_j in 𝕋$. Because the weights $μ_j$ are positive and sum to $10$,
$
  ∑_(j=1)^3 μ_j , abs(f(z_j))^2
  ≤ ∑_(j=1)^3 μ_j = 10.
$

Combined with the weighted square-sum identity, we obtain:

*Theorem* (Core inequality).
  For any polynomial $f(z) = a_0 + a_1 z + a_2 z^2 + a_3 z^3$ bounded by $1$
  on $𝕋$, and for the unimodular parameter $ξ$ constructed in
  Section~4.1,
  $
    6 norm(a_1 + a_2)^2 + 9 norm(ξ a_0 + a_3)^2 ≤ 10.
  $

_Proof_.
  The three nonnegative terms on the right-hand side of the weighted identity
  are $abs(a_0+2a_1-2a_2-a_3)^2 ≥ 0$,
  $6 abs(a_1+a_2)^2 ≥ 0$, and
  $9 abs(ξ^* a_0 + a_3)^2 ≥ 0$.
  Discarding the first term and applying the bound
  $sum μ_j abs(f(z_j))^2 ≤ 10$ gives
  $6 abs(a_1+a_2)^2 + 9 abs(ξ^* a_0 + a_3)^2 ≤ 10$.
  Taking norms (which equal absolute values for complex numbers) completes
  the proof.

== Completion of the upper bound

We now assemble the pieces.

*Theorem* (Upper bound).
  $S({0,1,2,3}) ≤ 5/3$.

_Proof_
  Let $f(z) = a_0 + a_1 z + a_2 z^2 + a_3 z^3$ satisfy
  $norm(f)_∞ ≤ 1$. By the reduction in Section~4.1, we may assume
  $norm(a_1) + norm(a_2) = norm(a_1 + a_2)$ and
  $norm(a_0) + norm(a_3) = norm(ξ a_0 + a_3)$ for some $ξ in 𝕋$.

  The binary Cauchy--Schwarz reduction (1) gives
  $
    (∑_(j=0)^3 norm(a_j))^2
    ≤ (6^(-1) + 9^(-1)) (
      6 norm(a_1 + a_2)^2 + 9 norm(ξ a_0 + a_3)^2 ).
  $
  The core inequality (Section~4.5) gives
  $6 norm(a_1 + a_2)^2 + 9 norm(ξ a_0 + a_3)^2 ≤ 10$.

  Therefore
  $
    (∑_(j=0)^3 norm(a_j))^2
    ≤ (frac(1,6) + frac(1,9)) dot.op 10
    = frac(5,18) dot.op 10
    = frac(25,9).
  $
  Taking square roots yields $sum norm(a_j) ≤ 5/3$, as claimed.

== The lower bound

For completeness we recall the lower bound established by Neuwirth
@neuwirth2026fourieranalyticsidonconstant.

*Theorem* (Lower bound).
  $S({0,1,2,3}) ≥ 5/3$.

*Proof*.
  Consider the one-parameter family of polynomials
  $
    f_tau(z) = frac(i 2 √2 cos tau - 1 - 3 sin tau, 15)
    + frac(3 + sin tau, 10) z
    + frac(3 - sin tau, 10) z^2
    + frac(i 2 √2 cos tau - 1 + 3 sin tau, 15) z^3,
  $
  parametrized by $tau in RR$. A direct verification shows that
  $∑_(j=0)^3 abs(c_j) = 1$ independently of $tau$. Setting
  $Phi(t,tau) = abs(f_tau (e^(i t)))^2$, an algebraic computation yields
  $
    & Phi(t,tau) = frac(2 √2 sin(2 tau), 75)
    (sin t - sin 2t + 2 sin 3t)
    + frac(247 - 13 cos(2 tau), 900) \
    & quad + (1 + cos(2 tau))(frac(cos t, 20) - frac(cos 2t, 25))
    + frac(1 + 17 cos(2 tau), 225) cos 3t.
  $
  Solving the critical point equations $(partial Phi) / (partial t) = 0$ and
  $(partial Phi) / (partial tau) = 0$ shows that for each $tau$, the global
  maximum of $Phi(t,tau)$ is $9/25$, attained at exactly three points on
  the circle. Hence $norm(f_tau)_∞ = 3/5$, and the ratio of coefficient
  sum to supremum norm is $(1)/(3/5) = 5/3$. The Sidon constant, being the
  supremum of such ratios, is therefore at least $5/3$.

Together with the upper bound, this completes the proof of the Main Theorem:
$S({0,1,2,3}) = 5/3$.

= Formalization

The entire proof of the upper bound (Sections~4.1--4.6) has been formalized
in Lean~4 using the mathlib library. The formalization consists of five source
files.

== Module structure

The formalization mirrors the logical structure of the paper:

- `Polynomial/SelfInversive.lean` defines self-inversive polynomials and
  proves the disk/sphere lemma. This uses the root symmetry property ($r$ is
  a root iff $1/r^*$ is) and relies on mathlib's C\*-algebra norm library
  for $norm("lc"(P)) = norm(P(0))$.

- `Polynomial/Cohn.lean` proves the Blaschke product estimate and uses it to
  establish: for a self-inversive $P$, the roots of $P$ lie on the unit
  sphere iff the roots of $P'$ lie in the closed unit disk. The proof
  constructs an algebraic identity relating $P$, $P'$, and the reversal of
  $P'$, then applies the Blaschke estimate.

- `KeySystem.lean` is the heart of the proof. It defines
  $psi = (ξ+1)/4$, the cubic $P(X) = X^3 - psi X^2 + psi X - ξ$, and its
  derivative $Q$. It proves $P$ is self-inversive and separable, that the
  roots of $Q$ lie in the open unit disk, and hence (via the Cohn lemma) the
  three roots $z_1, z_2, z_3$ of $P$ lie on the unit circle. Vieta's
  formulas give the symmetric sum relations. The $Λ$ coefficients are
  defined and the four moment identities are proved using field arithmetic;
  the positivity of the weights is established by the rational simplification
  to $μ_j = 18/(6 - 2,Re(z_j) + Re(z_j^2))$.

- `SquareCoeffBound.lean` proves the weighted square-sum identity. Expanding
  $abs(f(z))^2$ on the unit circle as a Hermitian form, it evaluates the
  $mu$-weighted sum at the three roots, substitutes the moment identities,
  and simplifies to the sum-of-squares decomposition. From this and the
  hypothesis $norm(f)_∞ ≤ 1$, it deduces the core inequality.

- `Main.lean` assembles the final proof. It handles the two coefficient
  alignment reductions (using `NormedSpace.normalize` for unimodular
  rotation), states the binary Cauchy--Schwarz inequality, and chains
  everything together to obtain $S({0,1,2,3}) ≤ 5/3$.

== Design decisions

*Rational function computation.* The moment identities involve rational
expressions simplified under the side conditions $z_1 != z_2$, $z_1 != z_3$,
$z_2 != z_3$ and the root relations. The `field` tactic in mathlib, which
clears denominators and reduces to polynomial equations, handles these
cleanly.

*C\*-algebra norms.* The self-inversive lemmas use properties specific to
$ℂ$ as a C\*-algebra, in particular $norm(z^* z) = norm(z)^2$.
Mathlib's `CStarRing` typeclass provides this uniformly, and the proof of
$norm("lc"(P)) = norm(P(0))$ uses
$"lc"(P)^* dot.op "lc"(P) = P(0)^* dot.op P(0)$.

*Algebraic over analytic.* The proof that $Q$ has roots in the open disk uses
only elementary inequalities (triangle inequality and $abs(psi) ≤ 1/2$)
rather than general complex analysis. The Blaschke estimate is the only place
where root factorization is needed.

*Compilation.* The project is configured via Lake and depends on `mathlib`.
It compiles suℂessfully and the proof of the main theorem `Sidon3` can be
inspected directly.

= Further Questions

The exact value of the Sidon constant is now known for a handful of sets:
all sets of size $≤ 3$ @neuwirth2001sidonconstantsetselements,
${0,1,2,3}$ (this paper), and ${0,1,2,3,4}$ @shapiro1951extremal (value
$2$). Several directions remain open.

1. *Four-element sets.* Can the Sidon constant of an arbitrary four-element
   set be computed? The method introduced here relies on the fact that the
   cubic $X^3 - psi X^2 + psi X - ξ$ has all roots on the unit circle. For
   larger sets, one needs higher-degree self-inversive polynomials with all
   roots unimodular and carefully tuned Vieta coefficients.

2. *Real vs. complex unconditionality.* For ${0,1,2,3}$ in $C(𝕋)$, the
   real and complex unconditionality constants coincide (both equal $5/3$).
   This is also true for all three-element sets
   @neuwirth2001sidonconstantsetselements. Does there exist any subset of
   $ZZ$ for which they differ in $C(𝕋)$? The question is open even for
   $L^p (𝕋)$ with $p != 2$, and in particular for ${0,1,2,3}$ in $L^p$
   when $p$ is not a small even integer
   @neuwirth2026fourieranalyticsidonconstant.

3. *Sets with Sidon constant close to $1$.* The three-element result shows
   that one can achieve Sidon constants arbitrarily close to $1$ by taking
   well-chosen triples with large $n = max abs(Λ_i - Λ_j)/gcd$. For
   four-element sets, the minimum possible Sidon constant is unknown.

4. *Connection to Hadamard matrices.* The bound
   $S(Λ) ≤ sqrt(abs(Λ)-1)$ is sharp only when a circulant complex
   Hadamard matrix exists of appropriate size. This connects the Sidon
   constant problem to the existence theory of biunimodular sequences
   @bjorck1995new. Our result shows that for $n = 3$, the extremal
   configuration is _not_ of Hadamard type.

5. *Mechanization of the lower bound.* The present formalization covers only
   the upper bound. A complete formal verification of the Main Theorem would
   require also formalizing the lower bound, i.e., the verification that
   Neuwirth's extremal polynomials indeed have supremum norm $3/5$.

#bibliography("references.bib", full: true, title: "References")
