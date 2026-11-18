# A concrete common elliptic index for the actual scalar pole, all four guards and the exact row relaxation

**Explicit source input.** At a=0 or −1 take r=4376874610839020=4g,
g=1094218652709755, and use the source's natural A0=6,B0=0,d=1 and
the following actual integers:

    h=328655617654071015360,  J=h·g⁸·11·17,
    n=1+6²¹·3⁶⁵⁵³⁶·J.

Use FixedArithmeticLabels318.labels(a,6,0,3^65536·J); its second label
is n and its other entries are the prescribed inputBeta and the actual
positive odd Lucas witnesses, not (−1)^4 or freely selected roots.
The arithmetic below is independent of which valid Lucas representatives
are chosen. This h,n produce the *actual* scalarB, satisfying the
entire published AllScalarSupportPreparation318.Prepared and its strict
scalar real guard, plus all four literal detector trace guards. No
astronomical scalar numerator or elliptic multiple is expanded.
This is an explicit scalar-side witness, **not** a choice proven to
satisfy the other support, contact prime/order or real mixed CRT
requirements of the full construction.

## Scalar finite places and a compatible positive-index construction

At a=0,−1 the support of A=114444r is precisely
2,3,5,11,17,163,661,733,1489,1861. Its squareclass is
m=12036405179807305=11g, with A=204²m and m≡1 mod 8,3,17.
Write U_j=chartU(j), H=Norm U_h, c=Norm U_{n−1},
N=Norm(1+U_h²/r), Q=c/(H r^15), W=N²+rQ². The earlier exact order
table ORDERS.json is retained from forward-actual-index-depth-and-palettes-r1.
For p|g the common h is a multiple of every reduction order of P=2R at
w|p. The same is true at 11 and 17: the orders at 11 inert, at 17 with
√2=6, and at 17 with √2=11 are 5,5,2 respectively. These small prime
orders are prime and verified by nonidentity plus the annihilator
computation. R=(1+√2,2√2), y²=x³−δx, δ=(3−√2)². All these are primes
of good reduction. verify.py also uses projective arithmetic modulo p³ to
bound formal depth at each first entry. The last two output coordinates
record the valuation of the formal parameter and whether the reduction
at half-order is the special (0,0) torsion.

As n−1 is a multiple of h, both multiples are in every listed formal
kernel. With uniformizer p (unramified), the formal logarithm is an
isometry and x(jP)=1/U_j², so
v_w(U_{n−1})−v_w(U_h)=v_p(n−1)−v_p(h).
At p|g the latter difference is 8, v_p(r)=1; at 11,17 it is 1 and
r is a unit. Hence v_p(Q)=1 and 2 respectively. In every completion
v_w(U_h)>0 so 1+U_h²/r≡1 mod w. It follows that N≡W≡1 mod p.

At 2 use the actual source identities
v₂(Norm U_h)=v₂(Re(U_h²))=3+2v₂(h); m0=n−1 is nonzero and
v₂(m0)−v₂(h)=21. Then v₂(Q)=42−30=12,
N=1+(H/r)²+2Re(U_h²)/r≡1 mod2 and W is a unit.
At 3 both indices are even and nonzero;
v₃(Norm U_j)=2+2v₃(j) and v₃(Re(U_h²))≥v₃(H).
The index valuation difference is 65557 and r is a unit, so v₃(Q)>0,
N≡W≡1 mod3. W>0 and all divisions are genuine.

Now b=A(W/(1+A))² preserves v_p(A) on its support and has even
valuation everywhere else. Hence the reduced denominator is square,
(v₂(b),v₃(b),v₁₇(b))=(4,2,2), b has squareclass m square in all three
local fields, and W is a unit at every support prime. These are exactly
the clauses of the scalar Prepared definition, not just six sample
solubility tests. Source theorem PreparedIntegerSource318.scalar_domain
gives 0<b<17 once the following true scalar norm guard is verified.
The earlier coherent full-Selmer producer therefore applies at this
explicit indexed b itself, with β=17m and the actual D=1−b/17. It gives
a genuine nonzero first rational point and a fixed partner in full
2-Selmer, not the still-missing second rational point.

## Independent two-sided real enclosure

real_enclosure.py uses a 2,000-bit dyadic grid. Every multiply/divide
is rounded outwards, with zero exclusion checked at every division;
integer square root supplies rigorous brackets for ±√2. In both real
embeddings repeatedly double/add R along the binary digits of **h**
and substitute U_h=2y/(x²+δ). With endpoints in multiples of 10^−15,
the product of the two real embedding intervals is bounded by

    −50452284917358 ≤ 10^15 Norm(U_h) ≤ −50452284917357.

It therefore exceeds 1/100 in absolute value. This is not a decimal
heuristic or an independent choice of U_h. REPLAY.json contains both
individual embedding bounds.

## The four trace denominators never vanish at any original integer index

For all nonzero integer labels j, at every integer h the real coefficient
of the corresponding literal denominator equals

    Re(U_{j(h−1)}²)−Re(U_{jh}²),     with Re(U_0²)=0.

For k≠0, source half_trace_two, chart_norm_two and common_norm_ne yield
v₂(Re(U_k²))=3+2v₂(k). For adjacent h,h−1 one integer is odd and the
other even. Away from h=0,1 the two displayed terms have distinct
valuations, and the smaller is 3+2v₂(j). At the two endpoints one term
vanishes, the other has the same stated valuation. Thus the denominator
is nonzero with that **exact** dyadic valuation. These are ALL four
required rational trace guards of RealGuardWitness318, for the very same
h, without using a real neighborhood argument or computing the enormous
Lucas labels. This does **not** remove the separate strict real norm
inequality, here established by certified interval arithmetic.

A separate short source candidate UniversalDyadicGuard318.lean proves
the nonvanishing variant when elaboration succeeds; this packet's
paper argument does not claim Lean acceptance.

## Precise status of the 284-row relaxation

For fixed h above, take the compact singleton consisting of the actual
projected detector witness in ThreeDetectorUniformFamily318.uniform_family.
That source result with the established guards proves, for every
sufficiently large rational contact parameter T, the 248 pre-pole rows
and strict 0<b_i<17 at all three actual detector pole slots 190,241,292.
The scalar fill gives r263..281 at the same earlier slots. For each of
the four positive b_i independently choose a common parameter for the
two equations of its own block and a global first rational ordinate:
e.g. at B_i=17b_i the first point with
e_internal/B_i=(1−B_i v²)/(1+3B_i v²), y=4B_i²v/(1+3B_i v²)
works for any v≠0, with v small enough to keep parameter nonzero.
At the scalar block one can instead use its stronger coherent full-Selmer
choice. Set the original e_slot=e_internal/b_i and p_slot=y/B_i.
Choose any rational s_slot≠0,q_slot (the latter need not pass the
second equation). Fill each block's e_slot·b_i, s_slot² and original
factored product times −1/3 as in ThreePoleCertificates318.fill and
ScalarCompleteSource318.finish. This is an assignment of raw slots,
**not** an invocation of an already complete Certificate.

The 248 previously verified rows ignore those new slots, and the
scalar nineteen also are preserved. The displayed block definitions
and their source ring identities give r152,153,154,155; r205..208;
r258..261 and r282..285, the three bookkeeping rows and first square
in each. For the physical final row at the source's actual scale, the
current labels have exactly the multiplier shape in ActualAnchorAllPlaces318.
Its actual_all_places gives local representations at infinity and every
finite prime. The classical Hasse–Minkowski theorem for quadratic forms
provides a nontrivial rational homogeneous point (the zero right-hand
constant case is immediate); the existing rational anisotropy/affine
normalization and PhysicalAnchorFromHomogeneous318.currentAnchor give
the three rational slots for r287. In particular we are using the
classical theorem in this mathematical count, not claiming new kernel
elaboration of its wrapper.

Consequently the single assignment satisfies **284 of the 288 literal
rows**; only r156, r209, r262, r286 (four second squares) are not proved.
It is an existential family indexed by large rational T, not a fully
printed 318-entry vector. This count is a relaxation, not evidence
alone for a new hard-step solution: for every integer input a the same
count was available already with the trivial first certificate e=17,p=0,
actual label-shaped local-global anchor and a legal detector witness.
The distinct gains here are an explicit actually Prepared scalar index
at the two chosen a, a spot-checked strict real guard, universal guard
nonvanishing, and a coherent global first point/full Selmer partner on
this indexed scalar. Positivity of the three other b_i alone does NOT
give their square-denominator/selected prime contact data or an
everywhere-locally-soluble marked partner on them.

## Exact local criterion versus already prepared CRT

For p∤2·3·7·11·17, k=v_p(r)>0 odd, a local rational PointPair is
possible exactly when v_p(B)>0. Necessity is the fixed-label lock;
sufficiency follows because D=1−B/289≡1 modulo p is square: taking
e/B=(1−B)/(1+3B), s=B√D, y1=4B²/(1+3B), y2=y1s³ gives both ordinates
nonzero. At k=1 this means hP enters the formal kernel at every w|p and
v_p(c/H)≥15. At an inert place the criterion is exactly o|h,n−1 and
v_p(n−1)≥v_p(h)+8. For 1489 at these inputs the component orders are
178 and 389, first entry depth 1 each; [89]P at √2=382 is (1110,0),
not (0,0), and the other group image has odd order. Thus no nonformal
multiple has x=0 in reduction and its U valuation is zero. If exactly
one component is active for n−1, local solubility requires, and for
h formal in both is equivalent to, v_p(n−1)≥2v_p(h)+16:
the two order integers are units at 1489, so the active contribution is
1+v_p(n−1) versus 2+2v_p(h) for H. With both components active, the
difference bound is 8, as above. Our explicit choice uses both.

Beware: the published Prepared itself already forces v_p(W)=0 for all
p|A. At odd k this gives v_p(N)=0, v_p(Q)≥(1−k)/2 and, by the exact
norm-deficit formula, v_w(U_h)≥(k+1)/2 at all w. The formal-log comparison
then sharpens to v_p(n−1)−v_p(h)≥ceil((29k+1)/4). The actual
AllScalarDetectorJoin318.integer_preparation already supplies
**all** h≡h0 mod L as Prepared; both h0 and h0+L are positive, so the
whole lcm of compulsory reduction orders divides **both h0 and L**,
not just their radicals. These explicit order filters screen as-yet
unprepared candidates; they are not new failures for a correctly
prepared record that has already imposed gcd(Mplus,L)=1. For each fixed
nonzero h, irrespective of n, the local pair bound alone forces every
good odd-depth p|r(a) to divide the numerator of Norm U_h. By the
previous factorization and genus-three Faltings argument there are only
finitely many possible integer inputs a at that h. The source may vary
h and its multiplier after a; no global impossibility follows.

## Source and replay

Run python3 -B verify.py and compare output to REPLAY.json.
The exact source circuit and charts are at Git commit
a0950ac7c24df6d336a196966fb790d6abd55e44. Beyond the dependencies
already pinned in forward-actual-fixed-label-pointpair-obstruction-r1:
the two/three half-trace sources in forward-scalar-index-preparation-r2
have hashes ae3e5e0de7f42f554e2a5fb4cff7515671f19f1c384d968fd8b682d83d96ce65
and 9cdb43f04b037d453a100c9eacca01eaabe874159005771c3e1481bf90ed21af
(ScalarHalfTraceDepth318 and ScalarIndexValuations318).
In forward-actual-ambient-primitive-lifts-r1, AllScalarSupportPreparation318
and AllScalarDetectorJoin318 hash db7793cdd7327ad737a3312dcda0962096a803ddca61caf8ba90d1657604c677
and 36f345e2d74e522d46c20cd3a5cba49f31642355d5209dfbb0be6a71748f2c41;
ThreeDetectorUniformFamily318 and ThreePoleCertificates318 hash
7d0fdb0b714b8b29985337d12bb5c35858019b59179088b1e9ebfbac10c80e64 and
8509834b98d623cf0fa0208bd06ac02f30084305d25bc895d2a87232dcfa3c68.
No local Lean was run; conditional source implications are distinguished
from newly elaborated declarations.
