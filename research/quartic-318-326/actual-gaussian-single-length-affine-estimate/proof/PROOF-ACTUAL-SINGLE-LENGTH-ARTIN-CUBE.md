# The actual single-length affine Artin cube, and the integrated old PET endpoint

This is a paper application of unconditional Frei–Tinková and classical
ray class reciprocity, not a checked Lean formalization of either.
The appended source consumes exactly its conclusion, without an interval
of widths, an affine estimate uniform in the ray field, or an assumption
of a fixed-cutoff nonlinear prime theorem.

## 1. Exact family and arithmetic mean

Fix the original geometric choices, original total step dilation and
already folded distinct coefficients, thin aspect ratio, selector cutoff
s, and its fixed Gaussian ray data before choosing y and N. Let
K_s/Q be the full rational-conjugation-invariant Gaussian ray field for
the actual modulus M_ray=16R, with odd squarefree R at the chosen
minimal base; C_s is the stipulated union of actual ray conjugacy
classes. The actual norm predicate is membership of rational Frobenius
in C_s at unramified primes. The coarser inert option may use the
independently specified conjugacy union in the projected field (or its
preimage in the full field). Use exactly one such option in both ray
and mean. This is not inferred from the one-way native SelectedOrbit
or Realizes interface for an arbitrary Family.

The explicit prior conductor computation in
ray-exact-abelian-conductor-r1/EXACT-GAUSSIAN-ABELIAN-CONDUCTOR-AND-ORBIT.md
gives K_s^ab=Q(zeta_(32R)); it uses ray reciprocity, unit quotient,
conjugation action, and the ideal-norm congruence modulo 2M_ray.
Use F=32R in the source Family. If a separately specified actual Artin
field has abelian conductor D dividing its source period F, the same
argument below works with that D and that same F. In all cases choose
y large enough for every prime of F to divide W=prod_(p<=y) p.

With the field and union just chosen, define the source fiber at a unit
residue b by

    mu(b) = phi(F) sum_(C in C_s) eta_(K_s,C)(b,F).

Set it to zero on nonunits. In the exact Gaussian case F=D, formula
(1.10) in [Frei–Tinková v3](https://arxiv.org/html/2408.17441v3)
says that this is the number of elements of C_s in the corresponding
abelian fibre divided by |Gal(K_s/Q)'|. The finite Gaussian norm-fibre
counts in the conductor receipt and the exact period-16 reference
series therefore give precisely the same function, not an unrelated
Chebotarev density. The ratio lies in [0,1]. For D|F the same value
at unit residues is phi(D)sum_C eta(b,D), by their Lemma 3.5. There
is no need to divide by this conditional probability when it is zero.
This describes the arithmetic construction of the actual Family on
paper; native global class-field construction is outside this packet.

## 2. One actual length, exact signed wrap and lattice cells

Use the literal old row n=floor(N/W), 1<=b_i<=W,
gcd(b_i,W)=1, cut=ceil(n^rho), alpha=phi(W)/W, and the original
0<rho<1 choice. The upper restriction on rho is explicit here;
Family.hrho alone asserts just positivity. The folded polynomial
outputs are untouched; the affine input uses their same registered
residues and just the old centered x variable.

At exact order a test only

    J=CommonEnvelope.testJ(Family,B,a,y,N),
    1<=q<=CommonEnvelope.testQ(Family,B,a,y).

ShellReady yields qJ<=n and positivity. At each fixed y the original
fine subtract-one floor is at least c_y sqrt(N) eventually; the
inequality actually computed in the proof of common_length, before
its final weakening, is

    J >= [c_y^2/(2 (Astar(Family,B,y))^(2a))] N.

This is now separately recorded as linear_length. Because n<=N
and J<=n, J is comparable to n at that fixed y. In particular an
o_y(n^(1+2a)) remainder divided by Z=n J^(2a) is still o_y(1).
The weaker stated sqrt(N) bound alone would not support that passage.

Keep exactly independent endpoint digits h,h' in [1,J]^a, and one x
in [1,n]. For each vertex omega in {0,1}^a put

    L_omega=x+q sum_j omega_j(h_j-h'_j),
    w_omega=floor((L_omega-1)/n),  -a<=w_omega<=a,
    psi_omega=W(L_omega-n w_omega)+b_i.

The interval convention is 1<=L_omega-n w_omega<=n, including its
right end. First partition by the integer vector w, then by the
residue modulo F of each of x,h,h'. This retains every source point
exactly once. After substituting coordinate=residue+F z, strata are
integer points of convex bounded polytopes: original intervals plus
the actual affine wrap strips. Their d=1+2a parameter coordinates
fit [-C_y n,C_y n]; at every vertex their affine gradients are

    F W (1, q omega, -q omega)

and constants are O_y(n), uniformly over the old b_i and all
allowed q. Different vertices' gradients are nonproportional,
because the first coordinate is the same nonzero number and at
least one other coordinate differs. Coinciding numerical values at
specific parameter points cause no loss of finite complexity. All
psi_omega are positive on the exact polytopes, and each psi residue
modulo F is fixed. Empty cells contribute zero. We use the original
Z once after summing; neither triangular differences nor independent
copies of x are substituted.

## 3. Evaluation of every cell hybrid

On a cell D0 select genuine prime vertices S; at omitted vertices
use mu evaluated at that same cell. Use Theorem 1.4, (1.10), (1.15)
and Lemma 3.4 of [Frei–Tinková v3](https://arxiv.org/html/2408.17441v3)
for the |S| actual affine forms on D0. This is the unconditional
prescribed-Artin result, not its GRH-dependent primitive-root result.
Expand the fixed disjoint union C_s once at each selected vertex; the
number of resulting class assignments is fixed. Its uniform
bounded-size error is o_y(n^d): at fixed y, q is in a finite range,
all gradients/intercepts satisfy the required bounded-size constraint,
and S, cells and possible residues form finite sets. The convex
regions may vary with N. If S is empty, the hybrid is exactly its
comparison main and does not invoke the theorem.

The treatment of the three replacements costs o_y(n^d), uniformly
over these inputs:

* If a selected representative is below cut, then after fixing
  h,h', at most O_y(n^rho+1) x inputs remain. Every other genuine
  factor is O_y(log n) and every arithmetic mean is <=1. Pay at
  most O_y(n^(d-1)(n^rho+1)(log n)^(2^a)).
* The published weight includes proper prime powers. There are
  O_y(n^(1/2) log n) of them up to the actual positive norm bound
  Wn+W. Fixing the other d-1 coordinates and the power value
  determines at most one x because its slope is nonzero. Fixed
  exceptional primes, if present in the chosen finite encoding,
  have the same single value bound. Both errors times logarithmic
  weights are o_y(n^d).
* Replace the displayed physical polytope volume by its lattice
  count. Only unit cubes crossing one of its fixed number of
  boundary hyperplanes can contribute discrepancy; each hyperplane
  crosses O_y(n^(d-1)) cubes. For this last bound project along a
  coordinate with maximal absolute nonzero normal component: at
  fixed other unit intervals there are at most d+2 possible such
  unit cubes. Empty or lower-dimensional cells obey the same bound.

At the abelian modulus D, the forms' residues are fixed, so the
averaged factor in (1.15) is simply the product of D*eta at those
residues. The classes may have density zero. At every p|W, p∤D,
each residue b_i is a unit and the unconditioned local factor is
(1-1/p)^(-|S|). Consequently multiplying by alpha at each genuine
vertex gives exactly the arithmetic means, because

    alpha prod_(p|W,p∤D)(1-1/p)^(-1) = phi(D)/D.

When F is a proper multiple of D, use the equality of the unit
conditional densities in §1. No additional field or dyadic factor
remains. Thus the hybrid is

    #D0 (prod_all_vertices mu_omega) prod_(p>y) beta_(S,p)
       + o_y(n^d).

For p>y the first coefficient F W is a unit. If p∤q, a pair of
distinct vertices also has a 2x2 minor equal up to sign to
F^2 W^2 q, so each single divisibility event has measure 1/p and
each pair has measure 1/p^2. The union bound plus the first
Bonferroni correction, followed by multiplication by (1-1/p)^-|S|,
gives beta_(S,p)=1+O_a(p^-2) with a constant independent of q,y,F.
For p|q the same single events give beta_(S,p)=1+O_a(p^-1).
For large y all factors are positive, close to 1 and

    sum_(p>y,p|q) 1/p <= log(q)/(y log y) = O_{a,B,rho}(1/log y).

Indeed the actual uniform_frequency donor fixes D0' before y with
q<=W^D0', and the pinned elementary estimate log W <= y log 4
applies. The good tail sum_(p>y) p^-2 is at most 1/(y-1).
The product differs from 1 by O_(a,B,rho)(1/log y), using
|exp(t)-1|<=|t|exp(|t|); the assertion holds independently of the
number of fixed-conductor cells.

## 4. Center, thresholds and exact use

At each cell the expansion of the product of prime-minus-mean factors
is the alternating sum of its 2^(2^a) subset hybrids. The common
comparison main #D0*prod_all mu has alternating coefficient zero.
The modulus of its local-factor error is bounded by a fixed multiple
of #D0/log y because all means lie in [0,1]. Summing over the
disjoint original grid gives exactly Z in the count bound, not a
cell-count inflation of the uniform main error. (The number of cells
is fixed and may be used to sum the o_y(n^d) errors.) After dividing
by Z, the conclusion is

    |linearCube(r,i,a,q,J)| <= C_(a,B,rho)/log y + o_(s,y)(1)

uniformly across actual eligible rows, genuine i, and every tested q
at the **one** length J. This supplies Rate: after delta>0 has been
chosen by the integrated ordinary/PET argument, choose y0 so the
displayed first term is below half delta^(2^a), then each N0(y) for
the second half. The result used by source is only
linearCube<=delta^(2^a), not its absolute form. The boxNorm clips
with max 0, so the safe one-sided bridge uses rpow monotonicity
and does not require positivity of the signed power.

The frozen ActualTZOriginalAffineToMixed318 picks its tolerance
before y and N. ActualTZOriginalSingleLengthToMixed318.actual
takes the maximum of its original threshold and this actual affine
threshold, on the same Family, one normalization, and same δ.
It accepts the same signed dominated row factors and exact original
normalized mixed product. The earlier independently cold-checked
arbitrary-prefix Upper paper applies under 8Tσ<1 with
T=2 tagCap and d(y)>0. The integrated hSmall at b=tagCap already
implies 8Tσ<1: tagCap>=1 for the actual shape,
2 tagCap<=2^(2 tagCap)<=2^(a+2 tagCap), and σ>0. For all placement
bounds use the exact recorded 4(2t+2)^2 times the coefficient
and coarse constants, or a larger fixed cap; no y-dependent cap
is introduced. Strict width and ordinary moment premises are
otherwise unchanged.

Open native boundary: the actual fixed-field Artin theorem and its
instantiation (including class-field reciprocity), plus the
arbitrary-prefix physical/CRT/Mellin Upper producer, are paper
arguments only. The entire integrated source and this successor
are not yet Lean checked. The result here is the normalized actual
mixed-row input. The separate literal mixed telescope, ordinary
majorization of prime inputs, periodic positive reference series,
and original lower-versus-obstruction mass are not certified by this
affine computation alone. No quartic point or simultaneous prime
tuple is claimed by this packet.
