# Exact E=16 reference series and one-cell centered-cube interface

**Scope.** Original 318/326, source-only deterministic arithmetic
and a tighter conditional analytic boundary. The paper class-field
identity, genuine centered Chebotarev cube, and actual pointed
nonlinear estimate are kept separate. No local Lean, dispatch, push
or theorem of prime existence asserted.

## Exact same original reference series

Use the minimal permitted base B=16 b with odd squarefree b containing
all fixed exceptions and 3,7,17. The proof only uses the odd residues
mod their primes, so no higher powers of B's odd part are needed.
Fix selector cutoff s first, T_ray the product of new odd primes,
M_ray=B T_ray and R=b T_ray. The previous independently checked
paper conductor gives
        F = 2M_ray = 32 R.
The same abelian conductor applies to the optional split-ray plus
inert cyclotomic field; use the proper full-field preimage for old
full-modulus ArtinDatum. This equality is not produced by a native
semidirect group lemma. It has the exact paper reciprocity inputs
in the prior conductor receipt (reference below).

For the actual squarefree W=product_{p<=y}p whose support contains F,
write W=2V, V odd, R|V. The lcm is exactly 32V=16W, hence E=16
and F|16W. This is proved in source using the literal wheel;
odd prime support and squarefreeness supply R|oddWheel. It is not
safe to set E=16 before W contains every relevant odd prime.

For fixed s use mu_0=2/|G_B'|, b_0 equal to the norm of the actual
positive reference (same norm for its conjugate). Its exact
components are b_0=17 mod32, b_0=3 mod7, and b_0=1 at all other
odd primes of B. For each t prime to F, the actual conditional
arithmetic Frobenius density is
    mu_s(t)=mu_0 1_{t=b_0 mod 2B}
                 prod_{ell|T_ray} safe_ell(t mod ell)/(ell−chi_−4(ell)),
with mu_s=0 on nonunits. This is a conditional abelian-fibre
density divided by the commutator size, not a full-field
Chebotarev probability independently multiplied across outputs.
At optional inert ell the ratio is replaced by 1_{t≠1 mod ell}.
The source conditional interface takes exactly this mu_s as H.fiber;
it does not prove the global field classification.

In the old partialSeries use exactly the original shifted c'_i=q_step² c_i
and polynomial output U+d_i v², d_i=c'_i−K. The fixed shear
U=u+K v² is bijective at every local modulus, so the evaluation
of this series is still on the old (u,v) key. The exact CRT sum
from the previous source now runs over Fin(16W)^2, uses the SAME
compatible-row mask, and is divided by alpha^k(16W)^2 with
alpha=phi(W)/W. No separate treatment of the positive b=W boundary
or multiplication by 16² beyond the real box normalization.
CRT factorization is simply

    base = mu_0^k (2B/phi(2B))^k
           * Pr_{u,v mod2B}[all u+c'_i v²=b_0 mod2B]
    fresh ell = (ell/(ell−1))^k E_{u,v mod ell} prod_i
         [1_{p_i≠0} safe_ell(p_i)/(ell−chi_−4(ell))]
    ordinary ell<=y outside F = beta_ell of the same original forms.

This remains the old S_{s,y}, converging to the same fixed S_s by
the ordinary summable Euler tail. No independent density was assigned
to colliding shifts or independently chosen generators. In particular,
a zero base factor would be a true obstruction, not corrected by E.

Dyadic sanity/refinement: choose a fixed coefficient c'_0; all
p_i=17 mod32 iff u=17−c'_0 v² and all differences (c'_i−c'_0)v²=0
mod32. Writing d=min_i min(5,v_2(c'_i−c'_0)) (zero contributes 5),
the admissible v are the multiples of 2^r, r=ceil((5−d)/2).
There are exactly 2^(5−r) pairs, giving unnormalized density
2^(−5−r)≥1/256. The actual common q_step factors are included in
these valuations. The native equivalence counts one u per
admissible v; native four-site lower uses v=0,8,16,24, no
valuation interface needed. Neither this positive dyadic factor
nor the remaining finite CRT factors assert genuine prime mass.

On each old occupied row retain the exact periodic mean of the product,
now over a 16×16 block. The true strip error is
    A [((n/16)16)(m mod16)+(n mod16)m] ≤ 15 A(n+m);
the common old 16 A(n+m) interface remains sufficient. For the
real rows with dummy interval length I and coarse step length M0,
normalizing sum of strips gives at most 16 Z W(1/N+1/T_phys)
(or 15 via the sharper row lemma), where |J|/(alpha^k W²)≤Z.
This is independent of s in the period itself, not in any
prime-distribution threshold. It vanishes on a schedule W=o(T_phys).

## The exact surviving cube cells: ONE per wrapping pattern

For a fixed occupied row and prime-output label b_i (odd), the
actual conditional mu and actual genuine prime factor both vanish
unless W x+b_i=17 mod32 on canonical x∈[1,n]. W=2V, V odd,
so there is exactly one residue x* mod16. In particular the
existing centeredAt also vanishes off that residue. This statement
would be FALSE for unrestricted ordinary prime weights by themselves;
it is not a new restriction on the ordinary majorant.

For the old affine cube with q_cube≤qMax and order a use t=h−h',
eta=h', an invertible unimodular change on integer variables.
The exact original domain now has 1≤eta_j≤J and
1≤t_j+eta_j≤J, as well as the old x constraint. It remains convex in
each wrapped affine cell and preserves the original sum over all
h,h' and the normalizer n J^(2a); no triangular distribution is
dropped. Fix wrap integers m_omega on that cell. Let
        e_q=16/gcd(16,q_cube).
Refine only by x mod16 and t_j mod e_q; eta is not split. Each output
    L_omega = W(x+q_cube sum_j omega_j t_j − m_omega n)+b_i
has fixed conductor residue because F|16W and 16|q_cube e_q.
There are at most 16 e_q^a≤16^(a+1) possible residue classes
before support, versus 16^(2a+1) by refining all variables.

More strongly all actual centered vertices must hit 17 mod32.
The zero vertex fixes x mod16 uniquely; each singleton vertex
fixes t_j mod e_q uniquely if compatible (linear congruence
q_cube t_j=(m_singleton−m_zero)n mod16). Thus at most ONE of
these residue classes survives per wrap pattern. Higher vertices
can delete it, never add another. This support also holds for every
term of the centered expansion: every vertex contributes either
the ray prime factor or its supported mu, never an unrestricted
ordinary factor without the associated mu. After replacement,
every term carries the common product of conditional mu factors.
The native surviving_cell_unique proves this with two axis sets
and the same fixed wraps; no guessed wrap constant is imposed.

On the surviving cell the rescaled affine gradients are
    (16W, W q_cube e_q omega, 0 in the eta variables).
They are pairwise nonproportional on distinct omega; the eta
variables only describe the convex region. The same linear
modulus outside Wq_cube is unaffected since both 16 and e_q are
2-powers. All means are constant on the cell. This reduces the
finite geometric/conductor work, but not the required error
estimate for Artin primes and not its uniformity in changing s.

## Two separate analytic hypotheses on ONE common diagonal

Fix s, actual field, tau, original shifts and requested eps>0;
choose a, qMax and J-range per the exact existing proof. Examples
of the registered width hierarchy: A=W^(1/rho), A*=A^B0, use
the SAME coarse M0=floor(T_phys/W)−1 and fine M=M0/A,
J comparable to (A*)^(−2a) M², qMax≤A*^a, q_cube J/n<1.
The two remaining analytic statements are:

1. Centered linear: at the actual y(N), uniformly over all
   occupied rows, genuine output indices, allowed q_cube and J,
   the exact OriginalInteriorTelescoping.linearCube absolute value
   is <= delta^(2^a). On paper comes from fixed-field Chebotarev
   affine replacement plus ordinary cube local factors:
   C_a/log y+o_{s,y}(1) at each fixed y, then common slow diagonal.
   Use the original direct Gaussian linear proof or the separate
   [Frei–Tinková v3 Theorem 1.4](https://arxiv.org/html/2408.17441v3);
   no GRH primitive-root theorem. Apply at full wrapped affine
   cells with their actual support. There is no field uniformity.
2. Pointed nonlinear: on that SAME chosen diagonal, the above
   linear bounds at delta imply exactly k MixedBudget bounds
   eps*n*M0 for the old prefix product, with one distinguished
   centered genuine factor at each j and the actual zero-shift
   bounded dummy. The donor is published [Tao–Ziegler](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/B46C46EEC613F34152B7904E83EA0E3F/S2050508617000038a.pdf/polynomial-patterns-in-the-primes.pdf)
   Theorems 9, 11 (arbitrary-function model) and 13, Prop.4/Cor.3,
   plus ordinary majorant, matched to those shifts. This is
   neither qualitative affine-linear existence nor a deduction
   just from conductor arithmetic. It does not claim a fixed-y
   nonlinear continuation.

Use ONE y(N) slow enough for both analytic estimates and W=o(T_phys).
The theorem actual_mixed_on_common_diagonal merges the two
literal thresholds only; it supplies neither. The finite ledger
already uses eps chosen from S_s and the occupied-row scale,
S_{s,y}>=24S_s/25, I M0 W²>=3NT_phys/25; the same 16-period
rectangle now has an explicit s-independent width bound. The
old lower conclusion S_s NT_phys/10 and final medium/large-strip
margin follow conditionally without any reindexing changes.

## Exact source scope and controls

- ActualSquarefreeWheelConductor16318: literal wheel split,
  support divisibility, lcm, E=16, exact 15-strip upper at that period.
- ActualDyadicRayReference318: exact dyadic pair/v-fibre
  equivalence and four-site lower.
- ActualRayCubePeriod16318: explicit axis period and inverse,
  unique surviving cell, vertex conductor equality, exact
  unimodular change and residue-label cardinal.
- ActualRayPeriod16Interface318: original series specialized at 16,
  same-support centeredAt zero, original periodic allowance rewritten,
  and exact common-diagonal two-premise native interface.
- Direct donors preserved: CRT archive 445f0fe7…, conditional lower
  b476149a…, exact conductor 003331a4…, and independent dual-limit
  review joined-work-20261120/prime-lower-audit-r1/EXACT-LOWER-COMPARISON.md.
  The new code does not modify or claim to compile those archives.
- Arithmetic controls check literal lcm, wrapped vertex congruences,
  exact norm-17 dyadic fibres, shifted two-strip bounds and the
  one-cell uniqueness with inactive cases. No search for primes.
