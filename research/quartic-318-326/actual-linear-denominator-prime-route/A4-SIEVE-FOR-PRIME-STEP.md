# Original 318/326 alternative: elementary ambient A4 obstruction removal for one linear prime step

## Exact statement, and what it does not prove

Take r≥2 fixed integer homogeneous affine-coordinate forms L_j(u,q)
on two integer variables, with every pair of gradients nonproportional.
The proposed genuine prime-step system has one form q and the distinct
literal contact forms u+C_j q. The rational prime value of each form
must be positive, split in Z[i], and in [cN,N] for some fixed c>0.
A fixed-aspect region, u comparable to N and q in [ε₁N,ε₂N] with
0<ε₁<ε₂ suitably small and chosen before s, suffices. The statement
uses one choice of Gaussian coordinates for each true prime, one log
per distinct form (including q if it is a genuine extra form), and
one weighted term per original rational key (u,q).

Let a selected directed label be a translated norm (a_j±1)²+b_j².
An obstruction is common divisibility by an odd prime ℓ>s of two
labels at distinct forms, or of the opposite labels at one form.
A finite specified family of such constraints is allowed. This
does NOT include comparing one label to itself at the same position.
No obligatory generator choice has to be unique as a theorem of number
theory: fix one actual allowed orientation for each position and key,
and make all comparisons with those SAME chosen coordinates. The
upper bounds hold even when that choice varies with the key.

There is a constant A, depending on the fixed linear forms and finite
labels but not on s, field, or c, such that for all sufficiently large
fixed s, the genuinely weighted union of these remaining obstructions
at scale N is at most

    A N²/(s log s) + o_c(N²).

One can take Y=z=B^(1/20) with B=ceil(sqrt N), split at ℓ≤Y
inclusive, and take the error O(N^(2−1/40) log^(r+1)N).
This theorem neither produces Artin-prime lower mass, nor proves the
prime-step Padé valuation mechanism, a point, a rank, or a quartic.
It is unrelated to the nonlinear quadratic-in-step lower theorem until
the different proposed parameter t=u/(D²Q² q) is justified. q stays a
genuine separate prime; this proof does not insert it into a Π³ factor.

## One A4 injection, including q and the same-position case

For two distinct form indices i,j write their observed Gaussian
coordinates as a,b,c,d. The norms s₁=a²+b², s₂=c²+d² are exactly
L_i(u,q),L_j(u,q). Since the pair gradients have nonzero determinant,
they determine (u,q) uniquely (there is no need to reconstruct a
norm representation of q to upper bound). If a requested event is
same-position, use any one other genuine distinct form as companion.
This injection retains the SAME addresses and counts them at most once
for each fixed tag and ℓ. The number of tags is fixed. Enlarging the
carrier to the complete integer box [−B,B]^4 is only for upper bounds.
Translations a±1,c±1 are literal, and no orientation is reselected
per sign or local residue.

For a fixed odd ℓ, cross-position incidence selects at most
(2ℓ−1)²≤4ℓ² residues of the A4 box: the translated norm-zero equation
over F_ℓ is either two lines, or only (0,0). Same-position opposite
incidence gives 4a=0 and b²=−1, hence at most 2ℓ² residues with the
companion unrestricted. This includes inert ℓ (possibly empty).
Divisibility by ℓ is represented by those literal affine residues,
not by any marginal independence in the actual prime array.

## Large primes: no six-dimensional quadric estimate

In a single translated plane, solutions over F_ℓ lie in at most two
branches, each an affine lattice coset; in the inert case one branch of
the lattice ℓZ² suffices. The difference of any two distinct lifts in
one branch has positive squared length divisible by ℓ. Hence their
Euclidean separation is at least sqrt(ℓ). Squares of side sqrt(ℓ)/2
contain at most one such point, and O((1+B/sqrt(ℓ))²) squares intersect
the translated box. Every shifted norm on a genuine observed prime
is nonzero (a±1=b=0 would force original norm 1), and is at most 9B²
for B≥1. Thus only ℓ≤9B² occur, and the preceding upper is
O(B²/ℓ) uniformly over that range. Distinct-position bad tuples
therefore number O(B⁴/ℓ²).

For a same-position pair, ℓ divides a; the genuine prime p=a²+b² has
a≠0 (otherwise it is a square). Therefore ℓ≤B. The a multiples and
at most two residue classes for b give O((1+B/ℓ)²)=O(B²/ℓ²) points
in the first plane. The unrestricted companion has O(B²) points.
This is O(B⁴/ℓ²) as well. Summing over ℓ>Y gives O(B⁴/Y) before the
fixed log product. This retains all possible sign choices (finite
union) and does not invoke a rank-six Birch/Browning–Loughran input,
geometric sieve, primitivity, Gaussian UFD, or the old rank-five r41
tail. It would NOT suffice at the original old u,v box of size B³.

## Medium primes: actual rank-two plus rank-four local densities

Fix a pair i,j and write L_a(u,q) as A_a s₁+B_a s₂ with rational
coefficients. Multiply by fixed integer denominators to get integer
forms in a,b,c,d; this changes no sieve hits outside finitely many
denominator primes. Enlarge the fixed exceptional set E to include 2,
all relevant determinants and all coefficients needed to keep both
A_a,B_a nonzero when a≠i,j, and all primes ≤4r if needed. Choose s
greater than these primes. For p∤E, the two observed forms are
rank-two (the two separate norms), and every other form has two
nonzero coefficients. Distinct gradients stay nonparallel in the
(s₁,s₂) coordinates.

Let χ=χ₄(p). The count of norm representations of t∈F_p is
R(0)=p+(p−1)χ and R(t)=p−χ for t≠0: in the split case use
the product of the two linear coordinates a±ιb; in the inert case
use the surjective finite-field norm with kernel p+1. For a two-norm
sum with both coefficients nonzero, the zero locus consequently has

    R(0)²+(p−1)(p−χ)² = p³+p²−p

points, independent of χ. Each observed form has R(0)p² points.
An intersection of two distinct forms forces s₁=s₂=0 by their
nonparallel gradients; it has R(0)²=O(p²) points. Bonferroni union
bounds therefore give the exact needed first-order density of at
least one vanishing form in F_p⁴:

    g(p) = [r+2χ₄(p)]/p + O_r(p^-2).

Here g(p)>0 and g(p)≤1/2 after a further fixed enlargement of E.
Thus the sieve dimension is r, not r+2 and not r−2. An upper treating
both observed forms as rank four at every p would miss the true local
χ contribution. All prime outputs, including q if present, eventually
exceed z because their fixed-aspect lower bounds are cN.

## Exact finite Selberg upper and uniform main denominator

Fix s<ℓ≤Y and its actual bad slice Ω_ℓ above. For squarefree d made
from allowed primes p∤ℓE, write g(d)=∏_{p|d}g(p), and A_{ℓ,d}
for box points satisfying Ω_ℓ and the ordinary divisibility test
at every prime of d. Rectangle CRT gives exactly |Ω_ℓ|d⁴ g(d)
residue classes mod ℓd, independent of the old branch orientation.
For M=ℓd≤B, a single 4D residue class count differs from (2B+1)^4/M^4
by O((B/M)^3): each coordinate count is (2B+1)/M plus an error ≤1,
and expand the four products. Thus, using g(d)≤1,

    A_{ℓ,d} = (2B+1)^4 (|Ω_ℓ|/ℓ⁴) g(d) + O(B³ d/ℓ).

For real λ_d supported on those squarefree d≤z with λ_1=1, the
indicator of having no small allowed divisor is pointwise bounded
by (∑_{d|F_values} λ_d)², where F_values is the product of the
integer polynomial evaluations. Expansion uses d=[d₁,d₂]≤z², so
ℓd≤Yz²≤B. Exact quadratic-form diagonalization gives a useful λ:
define γ(p)=(1−g(p))/g(p), extend multiplicatively,
t_m=∑_{m|d} λ_d g(d), and G=∑_{m≤z}1/γ(m) over this finite
squarefree support. Then

    ∑ λ_d λ_e g([d,e]) = ∑ γ(m)t_m²,
    λ_1 = ∑ μ(m)t_m.

Choose t_m=μ(m)/(γ(m)G). Backwards finite Möbius inversion gives
λ_d g(d) = μ(d)G_d(z/d)/(γ(d)G), where G_d is the positive
same sum restricted to factors coprime to d. Thus the quadratic
main is 1/G and |λ_d|≤∏_{p|d}(1−g(p))^-1≤2^ω(d)≤d.
No sign replacement of the genuine density is made.

For G≳(log z)^r uniformly in the removed prime ℓ, use independent
multiplicative weights h(p)=g(p)/(1−g(p)) on primes up to z^δ,
δ>0 fixed and small. Divide by ∏(1+h(p)); each p is included with
probability g(p), so the expected log of its squarefree product is
∑ g(p)log p≪log(z^δ). Taking δ sufficiently small, Markov gives at
least half the weight to d≤z. The unrestricted weight here satisfies

    log ∏(1+h(p)) = ∑ g(p)+O(1) = r log log(z^δ)+O(1).

The O(1) is uniform in ℓ: deleting ℓ changes one factor by at most 2;
E is fixed. For completeness, no PNT in AP is needed for this
comparison. Elementary Chebyshev yields π(X)≪X/log X and
∑_{p≤X} log p/p≪log X. At σ=1/log X, comparison of the p≤X terms
of ∑p^(-1-σ) and ∑1/p costs O(1). The p>X tail is bounded by
partial summation and ∫_X^∞ dt/(t^(1+σ)log t) = O(1). The absolutely
convergent Euler logarithm for ζ at 1+σ then gives
∑_{p≤X}1/p=log log X+O(1) since integral comparison bounds ζ
between 1/σ and 1+1/σ. Apply the same estimates with |χ₄|≤1 to
the Euler logarithm of L(1+σ,χ₄). This is bounded: the alternating
Dirichlet beta series lies in [1−3^(-1-σ),1]. This gives
∑_{p≤X}χ₄(p)/p=O(1), uniformly. These classical Euler products are
only used at real 1+σ>1 with absolute convergence.

The total CRT error after the signed expansion has absolute bound
O(B³ z⁶/ℓ): z² ordered pairs, |λ_d λ_e|≤z², and lcm ≤z².
Sum over ℓ≤Y to obtain O(B³ z⁶ log(2Y)). The main upper is
O(B⁴/[(log z)^r ℓ²]); sum over odd prime ℓ>s by the elementary
Chebyshev bound in dyadic intervals to obtain O(B⁴/[(log z)^r
s log s]). Multiply by (log N)^r after the upper sieve, and add the
large tail. With z=Y=B^(1/20), the medium error is
O(B^(3+3/10) log^(r+1)N), while the large error is
O(B^(4−1/20) log^r N). This proves the stated weighted bound.

## Compatibility checklist for an original prime-step endpoint

* A true Artin lower output is still required. For the new fixed
  aspect region, the relevant lower form is at least c_s ε N² on
  one genuine common rational key set with c_s≳1/sqrt(s). Choose
  ε>0 fixed from geometry, Q, source height etc. BEFORE s.
  The preceding ambient upper has no τ factor and is nonetheless
  harmless: C/(s log s)=o(ε/sqrt(s)) for fixed ε.
* The old positive v=0 CRT witness cannot directly establish the
  new lower: q=0 would not be an allowable prime residue. Ensure
  Q² (times any fixed coefficient fold) vanishes modulo the whole
  fixed base conductor, incl. 32 and the relevant odd fixed
  exceptions. Then the contact forms equal u there, and one can
  take u in the fixed admissible base norm class and q in a unit
  class allowed by its own prime requirements. If that enlargement
  of Q is disallowed, this is a real local condition to check,
  not a conclusion of the sieve. Fresh field primes are above the
  finite exceptional set; the linear forms have distinct gradients
  and a positive common-unit residue fraction. The standard fully
  normalized Gaussian fibre loss still needs its actual datum.
* Small primes ≤s are handled by prior full selected ray conditions
  on the same chosen generators, not by the upper argument here.
  If the new q is order-only, use exactly the requirements needed
  for that external step; one may include its signed labels for a
  stronger upper but does not make that part of the rank/Π³ logic.
* The prime-step rational t, unit Padé charts, order valuations on
  both arms, exact scalar square denominator and subsequent point
  / rank machinery are separate. No such statement follows merely
  from existence of affine simultaneous prime values.

This elementary A4 sieve proof is an independent source check. In
particular it eliminates any need for a rank-six weighted quadric
or large-incidence sieve theorem for the *alternative*, but it is
not an alteration of the original frozen quadratic Pattern proof.
