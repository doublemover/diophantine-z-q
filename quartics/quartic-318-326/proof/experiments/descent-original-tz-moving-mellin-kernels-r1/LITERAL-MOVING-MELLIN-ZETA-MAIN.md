# Literal ordinary (68): moving-regulator cutoff and main integral, paper

Original quartic 318/326 only. This is the actual ordinary divisor
majorant, not a claim about nonlinear averages of primes or ray-primes.
Its only analytic ingredients are Schwartz inversion/decay, absolutely
convergent Dirichlet/Euler series on Re>1, and elementary comparison
with an improper integral. The formula is consistent with equations
(81), (82) and the §10.4–10.5 zeta ratio in Tao–Ziegler 2008; that
paper avoids truncation for its GENERAL terrible-prime case. Here the
actual linear x slope and wheel units give a uniform global raw bound,
so truncation is valid, with explicit order, before any near-pole
estimate. No zero-free region or uniform complex inverse zeta bound
away from the pole is invoked.

## 1. Exact inversion, all frequencies, exact original cutoff

Fix the ordinary source cardinal k, and the real even χ of the same
PublishedCutoff: smooth compactly supported in [-1,1], and
int_0^1 |χ'(u)|² du = 1. Let R=n^ρ>1 and L=log R≥2, fixing y and its
primorial W first. Let alpha=φ(W)/W. One long signed wrap has k
actual forms W*x+c_i, c_i=W*a_i+b_i, b_i a unit modulo W; all x
positions are shared. The exact CRT main (before the remainder) is

    D_R = (alpha L)^k sum_{d_i,e_i squarefree}
             density(d,e) prod_i μ(d_i)μ(e_i)
               χ(log d_i/L) χ(log e_i/L).

Here density is actual single residue density 1/Q when compatible,
0 otherwise, Q the squarefree union lcm over both slots. Although
written as a series this is literally the original finite cutoff
d_i,e_i≤R by support. For the Fourier transform choose the explicit
angular-frequency normalization

    g(u) = exp(u) χ(u),
    φ(ξ) = (1/(2π)) ∫_R g(u) exp(+i u ξ) du.

Then φ is Schwartz and inversion gives, for every real u,

    χ(u) = ∫_R φ(ξ) exp(-(1+iξ)u) dξ .

Thus exactly χ(log d/L)=∫ φ(ξ) d^{-s(ξ)} dξ, where
s(ξ)=(1+iξ)/L. The same sign and function appear in both slots;
there is no conjugation. For z=s(ξ), t=s(η), Re(z)=Re(t)=1/L
irrespective of frequency.

For fixed L>0 put σ=1/L. In one p-local nonempty assignment the
absolute amplitude is ≤p^-σ since at least one selected slot has
this magnitude and all others have magnitude≤1. The exact density
is 0 or 1/p at p∤W and 0 at p|W. There are only 4^k−1 nonempty
choices. Consequently the whole absolute multiple divisor series
at each frequency, uniformly in all imaginary parts, has bound

    ∏_p (1+C_k p^(-1-σ))
       ≤ exp(C_k sum_p p^(-1-σ))
       ≤ ζ(1+σ)^C_k ≤ (1+L)^C_k,    C_k=4^k−1.

In the middle inequality use the positive real Euler product
-log(1-u)≥u; the final inequality follows by integrating x^-1-σ
on [1,∞). This majorizes the ABSOLUTE assignment series, not just
the norm of its signed sum. Multiplying by the 2k integrable
Schwartz factors verifies Fubini and the exact result

    D_R = ∫_{R^(2k)} (alpha L)^k prod_p E_p(ξ,η)
             prod_i φ(ξ_i)φ(η_i) dξ dη .

The equality follows by first taking independent finite prime
universes and then absolute convergence; restoring χ after integration
recovers the original per-slot cutoff, not a different selection.
No cutoff is applied to d or p at intermediate steps. In particular
this argument does not impose a nonmultiplicative d≤R restriction
while distributing the Euler product.

## 2. Frequency cube vs scale hierarchy

Only AFTER the exact identity take H=L^(1/4). The complement of the
2k-coordinate cube |ξ_i|,|η_i|≤H has at least one coordinate outside
H. For any A>0, ∫_{|ξ|>H}|φ(ξ)|≤C_{A,χ} H^-A. Hence its exact
normalized contribution is, uniformly in W/cell/intercepts,

    O_{k,χ,A}( L^(k+C_k) H^-A ).

For instance choose A≥4*(k+C_k+2): this is O(L^-2), and choose any
stronger rate if desired. This is why absolute fixed σ convergence
alone would not justify the moving-regulator truncation; the extra
uniform (1+L)^C_k majorant does. The choice occurs after finite k
and χ are fixed, not after selecting some exceptional residue tuple.

## 3. Exact ζ quotient and uniform near-pole comparison

Write x=1/p, z_i=p^{-s_i}, w_i=p^{-t_i}. The precise one-position
reference prime factor B_i,p is

    (1-p^-1-s_i)(1-p^-1-t_i)/(1-p^-1-s_i-t_i).

At fixed σ each of the three ζ Euler factors converges absolutely,
and their nonvanishing in Re>1 follows from the same Euler series.
For all p, the product over i, then p, equals

    prod_i ζ(1+s_i+t_i) / [ζ(1+s_i) ζ(1+t_i)].

No phase choice for positive p changes this identity. To give a
uniform near-pole estimate without analytic continuation, for
Re(w)>1 and |w|≤2 use the absolutely convergent formula

    ζ(w) - 1/(w−1)
      = sum_{m≥1} [m^-w − ∫_m^{m+1} u^-w du].

The bracket has norm at most |w| m^(-Re(w)-1) by integrating
the derivative of exp(-w log u) inside the unit interval. Thus the
sum is bounded by 2 sum_{m≥1} m^-2, uniformly in this entire region.
For a nonzero shift v of positive real part put Z(v)=v ζ(1+v).
Then |Z(v)−1|≤2ζ(2)|v| when |1+v|≤2. On the cube, the three shifts
s_i,t_i,s_i+t_i are O(H/L)=O(L^-3/4) uniformly, so all corresponding
Z are nonzero and close to 1. Their main ratio factor is exactly

    ζ(1+s+t)/[ζ(1+s)ζ(1+t)]
      = (s*t/(s+t)) [Z(s+t)/(Z(s) Z(t))] .

If all three Z are within ε≤1/2 of 1, the bracket differs from 1
by at most 14ε: the product denominator has norm≥1/4, while
|A−BC| ≤ |A−1|+|B−1|+|B||C−1| ≤ (7/2)ε.
Multiplying by L gives the angular-frequency kernel

    K(ξ,η)=(1+iξ)(1+iη)/(2+i(ξ+η)),

with |K|≤(1+|ξ|)(1+|η|)/2 and uniform relative error O(L^-3/4).
Its k-fold product remains bounded by a constant times the product
of these first moments, and has the same O_k(L^-3/4) relative error.
The staged native residue-radius from Mathlib's residue theorem
also suffices for an unquantified uniform o(1); the explicit rate
above is the separate elementary paper proof.

The actual wheel replacement factor is exactly
alpha^k prod_{p|W} (prod_i B_i,p)^-1 because E_p=1 at such p.
For fixed W this is 1+O_{k,W}(H/L) uniformly on the cube:
p^{-s}=1+O(|s| log p) on Re(s)≥0 by integrating the derivative
along the segment from 0 to s, and finite denominators are uniformly
bounded away from 0. At s_i=t_i=0, B_i,p=1−1/p, so alpha^k cancels
exactly. The term O_{k,W}(H/L) is allowed to depend on the fixed y;
after fixing y it tends to zero. It is not a statement uniform in
a freely moving W.

## 4. Exact main integral and insertion of the true averaged tail

The identity for each original row is

    ∫∫ φ(ξ)φ(η) K(ξ,η) dξ dη
      = ∫_0^∞ (χ'(u))² du = 1.

Proof: replace the denominator inverse by
∫_0^∞ exp(-(2+i(ξ+η))u)du. On exchanging integrals the numerator
splits into the product of two identical angular-frequency
derivative integrals. Differentiation in the inversion formula
shows each inner integral is -χ'(u). For u≥0, Fubini follows from
e^-2u times the product of the two finite first absolute moments
of φ. The derivative exists by local dominated convergence, using
those same first moments and the exponential factor for u in a
small real neighborhood. The derivative is real, so square equals
absolute square; χ' vanishes for u>1. Neither a Plancherel constant
nor conjugation is missing. Tensor Fubini gives the k-fold kernel
integral 1 (and the empty product is exactly 1). Its tail outside
the same H cube is O_{k,χ,A}(H^-A) with the first absolute moments.

Let Q_off denote the off-wheel product of actual E_p / prod_i B_i,p.
For fixed positive σ, all products converge absolutely by the raw
factor bound / baseline factors; the exact finite ratio inequality
passes to the limit on an integer-distinct cell. For a nonzero
cell difference product D, put Xi=sum_{p>y,p|D}1/p. Previous literal
relative bounds yield

    |Q_off−1| ≤ U(D,y)=exp(A_k sum_{p>y}p^-2 + B_k Xi)−1.

Use this bound only for actual nonzero differences. Inside the cube
the normalized reference product (including the fixed wheel factor)
has norm at most a constant independent of y once fixed-y L is
large, times prod_i (1+|ξ_i|)(1+|η_i|). Split the complex error as
reference*(Q_off−1) + (reference−prod_i K). This keeps multiplicative
collisions inside a uniform first-moment bound; no illicit maximum
over tuples is used. For each retained cell the error is

    |D_R−1| ≤ C_{k,χ} U(D,y) + O_{k,χ,W}(L^-3/4) + O_{k,χ}(L^-2).

The actual normalized weighted average uses the same |I_r(z)|/n.
The reviewed elementary collision tail and quadratic good prime sum
then bound its first term by

    O_H( 1/log y + log^C(y+2)/y
                    + log^(C+1)(2N+2)/M ),

where C is fixed by the finite hierarchy. Short x and exact zero
differences contribute o_y(1) by their separate paper bound.
For long cells the old exact signed CRT rounding is
O_{k,χ}(L^k R^(2k)/n^(3/4)) = o_y(1) since 8Kρ<1 and k≤K. The
reference total over the retained cells has mass 1+o_y(1).
Thus this proves the ordinary FixedCutoffRate on paper, not native:
fix y large, then N sufficiently large at each y, uniformly in
actual eligible source branches/subsets, then take the common slow
diagonal using the previously ranked threshold. It does not establish
any nonlinear field-conditioned prime estimate or uniform fixed-y
o(1) after dropping e(y).

## 5. Native status / exact primary inputs

ActualTZMellinKernel318 stages the literal scaled kernel, denominator,
positive-half-line Laplace and exact sign. ActualTZZetaPoleRatio318
stages the true uniform punctured-disk radius from the pinned ζ
residue theorem, exact ratio factorization and 14ε sensitivity.
Both are Mathlib-only, source-only; no native transform inversion
application, Fubini integration of the kernel, absolute-series to
Euler bridge/global bound, finite wheel estimate, or full
FixedCutoffRate is asserted. In particular do not report a native
proof of the proof above from these two small modules.

Primary references read:
- Tao–Ziegler 2008 original §§10.4–10.5, (81)–(83):
  https://arxiv.org/pdf/math/0610050
- Pinned Mathlib RiemannZeta.lean lines 212–221 and exact Dirichlet
  EulerProduct lines 78–96:
  https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/LSeries/RiemannZeta.lean
  https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/EulerProduct/DirichletLSeries.lean
- Pinned positive-half-line complex exponential integral, lines 76–82:
  https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean
