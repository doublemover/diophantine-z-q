# Exact finite centered affine cube assembly (original 318/326)

Scope: deterministic source + checked arithmetic controls; no Lean run,
dispatch, push or assertion of the nonlinear theorem. All periods and
normalizers below belong to the old Family/Row, not a new cube model.
The frozen E=16 donor is archive 6e78f72c…, original paper audit is
joined-work-20261120/prime-lower-audit-r1/EXACT-LOWER-COMPARISON.md.

## Actual partition and one cell per wrap

Use V_a={0,1}^a, n=r.n, independent h,h'∈[1,J]^a, x∈[1,n],
t=h−h', and q the old cube frequency, not the original quadratic
step fold. The latter remains in r.ci and the immutable actual rows.
Put X_ω=x+qΣ_j ω_j t_j, m_ω=floor((X_ω−1)/n). Exactly
rep_n X_ω=X_ω−m_ω n, with the right end n included. Native
signedWrap_bounds uses qJ≤n, whence −a≤m_ω≤a; no assumption of
no wrap and no change to the old cube denominator Z=n J^(2a).
The code (m_ω+a)_ω has (2a+1)^(2^a) possibilities. All terms with
any vertex off norm 17 mod32 vanish before expanding, since both
genuine f and its exact old conditional mu vanish there.

For a realized active wrapping vector, the entire remaining finite
cell is EXACTLY the intersection of the usual convex wrapping
strips 1≤X_ω−m_ω n≤n and one pair of lattice conditions
x≡x_* (16), t≡t_* (e_q), e_q=16/gcd(16,q), for any actual
z_* in the cell. The forward implications are zero/singleton
vertices plus the old wheel W=2V with V odd. The converse is
all-vertex modulo-32 invariance since 32|16W, with the exact strip
test specifying the wraps. Holes are not overcounted. The same
congruences give all-vertex invariance modulo F for F|16W, so
the original means mu_ω are literally constant in this cell.

For the actual affine donor write
    x=x_*+16X, t_j=t_*j+e_q T_j, eta_j=h'_j,
with x_*,t_* represented canonically modulo their periods. Keep eta
in full. The inverse h_j=t_j+eta_j is integer and unique; the box
requires 1≤eta_j≤J and 1≤t_j+eta_j≤J. These constraints and all
wrap strips are affine inequalities; no averaging over t with
flat rather than triangular weights. The resulting convex lattice
cell has d=1+2a independent integral parameters, no new denominator
and no duplicate tags. Each physical form on it is
    Psi_ω=16W X+W q e_q Σ_j ω_j T_j
           +W(x_*+qΣ_j ω_j t_*j−m_ω n)+b_i.
Its gradient is (16W, W q e_q ω, 0). For q≥1 different gradients
are nonproportional: first components force the ratio 1 and a
differing j disproves equality. The condition r.cut≤rep_n X_ω is
another affine inequality for any selected genuine prime vertex.
The native cell identities involve the original r.cut and r.mu
through primeAt, never an unrestricted ordinary prime weight in
place of the genuinely supported f.

## Exact center cancellation (standalone Mathlib-only leaf)

For each cell D, select an ACTUAL point z_* and set mu_ω to the
original mean there. For a subset T of vertices carrying means,
form the original weighted affine hybrid
    A_T=(Σ_{z∈D} Π_{ω∉T} f_ω(z)) Π_{ω∈T} mu_ω.
The comparison B_D=#D Π_ω mu_ω is identical for every subset.
The all-means subset T=V_a agrees with B_D **exactly**, no theorem
about primes necessary. If a mean factor is zero, never divide by
it. The center sum in D equals
    Σ_T (-1)^|T| (A_T−B_D),
because Σ_T(-1)^|T|=(1−1)^(#V_a)=0, including a=0 where #V_a=1.
Thus if every hybrid error is at most Z·e, then the full original
cube has modulus ≤K_a e,
    K_a=(2a+1)^(2^a)·2^(2^a).
Empty actual cells give zero without asking an affine estimate.
The native proof sums over the original Fin(n)×Fin(J)^(2a);
it divides by this exact Z once, only after the reindex and bound.
This loose K_a depends purely on order, not s, field, wheel,
residue, tau, q, or box widths.

## What the fixed-field FT donor needs to prove

For each fixed selector field (s is fixed) and y large enough
for supp(F)⊂supp(W), use Frei–Tinková v3 §1.2 Theorem 1.4,
eq. (1.10)/(1.15), and Lemma 3.4:
https://arxiv.org/html/2408.17441v3
That is the unconditional Artin theorem, not the preprint's
GRH-dependent primitive-root result. The deterministic finite
assembly identifies the exact subset/cell hypotheses but does not
formalize the prime theorem or class-field correspondence.

* Fixed y: allowed q≤qMax(y) form a finite set, J≤n and J≥c_y n
  for all actual eligible J after a fixed-y threshold; at the old
  scale J≥n A^(−2B₀ a−7) up to fixed-y floors. The convex sets fit
  O_a(n) boxes with ambient dimension 1+2a; empty cells are skipped.
  The normalized intercept, gradients, signs and wrap variation
  are bounded at fixed y. Distinct selected gradients are
  nonproportional even after lattice substitution. FT's uniform
  bounded-size remainder o_{s,y}(n^(1+2a)) is thus o_{s,y}(Z)
  over the actual varying J, rows, and each allowed q.
* Form values on strips lie in [W+b_i,Wn+b_i]. The original r.cut
  can be intersected at selected vertices; on omitting a strip
  with rep_n X_ω<r.cut=ceil(n^rho), one X interval per fixed (T,eta)
  has length O(n^rho+1). Actual 0<rho<1 therefore costs
  O_{s,y}(n^(rho+2a) polylog n)=o_{s,y}(Z). Proper prime powers
  (and finitely many ramified rational primes if relevant) cost
  O_{s,y}(n^(2a+1/2) polylog n), since a prescribed power value
  has at most one X at fixed other coordinates. Independent
  of the shift's sign and relative slice size. Real volume can
  be replaced by #D at cost O_{y,a}(n^(2a)): each fixed number
  of boundary hyperplanes crosses O_y(n^(d−1)) unit cubes in
  the bounding box. These are absorbed into the single fixed-y
  threshold, not asserted to be rates uniform in y or field.
* The selected finite union of Artin classes may be expanded
  disjointly, with field/s fixed. On this congruence cell each
  selected residue mod F is fixed, every form unit at each p|W,
  and F uses the full actual abelian conductor. The FT F-factor
  per chosen vertex is (F/phi(F)) mu_ω; primes p|W with p∤F
  contribute (1−1/p)^(−1) each, hence cancel precisely the
  old phiRatio=phi(W)/W giving product of those mu_ω. The omitted
  vertices multiply their actual mu_ω; no radial multiplicity,
  ray normalization or field density is introduced.
* For p>y and p∤q the two rows of any distinct forms have a
  nonzero minor 16W² q e_q, so events of divisibility have
  pairwise probability p^-2. Inclusion/exclusion by the first
  two moments bounds the ordinary local factor by 1+O_a(p^-2).
  For p>y dividing q, each single form still has coefficient
  16W invertible, so union bounds give 1+O_a(p^-1). Uniformly,
  Σ_{p>y,p|q}1/p≤log q/(y log y), and actual
  log q≤log qMax=O_a(log W)=O_a(y) (fixed chosen exponent B₀).
  The total product differs from 1 by O_a(1/log y) once y large;
  the hidden constant may include the fixed scale exponents.
  This comparison acts on a main coefficient #D Π_ω mu_ω
  bounded by Z (actual 0≤mu≤1), so gives the standardized
  per-hybrid error |A_T−B_D|≤Z(C_a/log y+η) for any fixed
  η>0 once N≥T(y). If the residue cannot occur for a chosen
  class, its factor is zero, which the same comparison allows
  without division.

Consequently the exact native FixedCutoffRate is the literal
fixed-y external comparison plus valid positive n,J and
qJ≤n. Given that and ONE common schedule with y≥y₀, N≥T(y),
absorbed conductor, and C≤lambda log y eventually, native
linear_of_fixed_rate proves the actual original LinearOnDiagonal
provided K_a(lambda+η)≤delta^(2^a). For delta>0 take both scalar
budgets <=delta^(2^a)/(4 K_a) and slow y for T(y), then use y→∞
for the elementary log inequality. This says nothing about TZ
with y fixed, and supplies neither its pointed transfer nor the
full lower count on the quadratic pattern. No use of the
newly checked Fourier/quadric branch is made in this affine proof.

## Scope and regression

1. ActualCenteredCellCancellation318: Mathlib-only stand-alone
   exact centered inclusion/exclusion and subset error comparison.
2. ActualWrappedAffineCube318: actual signed wraps, cardinal,
   literal affine outputs, unique residue, exact converses and
   fixed means. Uses the frozen ActualRayCubePeriod16318 and old
   OriginalInteriorTelescoping318 through period-16 dependencies.
3. ActualAffineCubeDiagonal318: literal cell sum reindex, absolute
   centered cube, old normalized LinearBudget at all widths, and
   fixed-y rate specialization to the same common diagonal.
   No PointedTransferOnDiagonal premise anywhere in this packet.

Deterministically checked 108 cases, 72,927 exact points, 13,200
negative-wrap points, 552 retained points, 97 nonempty cells and
692 subset hybrids, including order zero and arbitrary retained
difference multiplicities. These are integer model checks of the
center/support/period arithmetic, not prime or asymptotic tests.
All source-only; no claims of Lean acceptance.
