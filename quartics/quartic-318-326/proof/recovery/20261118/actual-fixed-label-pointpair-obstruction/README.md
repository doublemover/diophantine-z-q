# Finitely many possible inputs at each fixed actual scalar root label

**Theorem.** Fix any integer n≠0,1. Allow the common integer chart
index h to vary freely, subject only to chartU(h)≠0 (in particular the
source real guard implies this). Only **finitely many** integer inputs a
can admit a rational NormalizedPolePoints318.PointPair at the *actual*
PreparedIntegerSource318.scalarB with second label n. This excludes
arbitrary rational free twist parameter, either ordinate possibly zero.
There is no effectivity assertion for the finite set. There is an
explicit computable necessary prime-by-prime filter. For example at
**a=0 and n=−1 there is no PointPair at any such h**, already over Q_5.
This label tests the actual scalar formula; it is not a proposed positive
affine label of the original construction.

At the eight residue classes 0,5,9,10,14,15,19,24 modulo 25 a stronger
necessary condition on *legal original positive labels* is

    5 | h   and   v5(n−1) ≥ v5(h)+8 ≥ 9.

**Quantifier limit.** The original strategy does NOT universally fix n:
AllPrimePreparedFullSource318.current_source takes a first, THEN chooses
a positive J, and permits a nonzero further multiplier d; its second
label is n=1+6^(A0+B0+15)·3^(2^16)·Jd. Hence at those inputs a
successful d=1 requires 5^9=1953125 dividing J, but the source CAN choose
J accordingly. No failure of the adaptive source theorem, all labels
at once, or the final 318/326 construction is alleged.

## Actual scalar map and a necessary valuation equality

Let r=inputR(a), L=114444=11·102², A=Lr, and put U=chartU(h),
H=Norm(U)≠0, J0=Re(U²) in K=Q(√2) (J0 is **not** the multiplier J).
At the actual detector inputs,

    N=1+(H/r)²+2J0/r=Norm(1+U²/r),
    c=inverseNorm(n)=Norm(chartU(n−1))≠0,
    Q=c/(H r^15),   W=N²+rQ²,   b=A(W/(1+A))²,
    B=17b,   D=1−b/17,   V=B²D.

For integer a, r>10, J0≥0, so N≥1,W>0,B>0. Indeed r≡5 mod17, hence
v17(B) is odd. The PointPair is y1²=F_e(B), y2²=F_(eV)(B s²) for
s≠0 and F_t(x)=x(x−t)(x+3t). The first equation excludes e=0
because B³ is not a square; the second similarly excludes V=0.
For p≠3, v_p(x) odd and t nonzero, a point with ordinate squared F_t(x)
requires v_p(t)=v_p(x): if v(x)<v(t) then v(F)=3v(x) is odd, and if
v(x)>v(t) then v(F)=v(x)+2v(t) is odd. Distinct valuations also exclude
zero factors, so the argument includes y=0. Apply to both x=B and B s²
whenever v_p(B) is odd. It follows that

    v_p(e)=v_p(B),  v_p(eV)=v_p(B)+2v_p(s),  v_p(V)=2v_p(s).

Thus v_p(D) must be even. For p∤3·17 and v_p(B) odd, it **cannot**
be negative, because v_p(D)=v_p(1−B/289)=v_p(B) would then be odd.
These are local obstructions to any pair, not just one anchoring method.

## Positive depth in the second label is forced, uniformly in h

Fix an odd p∤3·11·17 at which k=v_p(r)>0 is odd. Then 1+A is a unit,
v_p(B)=k+2v_p(W) is odd. The preceding necessity forces v_p(B)≥1.
The valuations of N² and rQ² have opposite parity, so
v_p(W)=min(2v_p(N),k+2v_p(Q)) without cancellation. It follows that

    v_p(N) ≥ ceil((1−k)/4),     v_p(Q) ≥ ceil((1−3k)/4).

Each place w of K over p is unramified; its normalized valuation of
r is k and its residue degree f_w satisfies Σ_w f_w=2. Accordingly
2v_w(U)−k is odd and cannot vanish. The norm identity gives exactly

    −v_p(N)=Σ_w f_w max(0,k−2v_w(U)) ≤ (k−1)/4.
    v_p(H)=Σ_w f_w v_w(U) ≥ k−(k−1)/8.

The latter follows by summing 2v_w(U)≥k−max(0,k−2v_w(U)). This handles
split primes and cases of different conjugate depths as well as inert
primes. Therefore the *same fixed* c=inverseNorm(n) must satisfy

    v_p(c)=15k+v_p(H)+v_p(Q)
          ≥ 15k + (7k+1)/8 + ceil((1−3k)/4)  >0.

At a simple prime k=1, the sum of the nonnegative deficits must be zero.
All v_w(U)≥1, so v_p(H)≥2 and v_p(c)≥17. At such p, having p^17 divide
the numerator of c is necessary, never asserted sufficient.

## Genus-three finiteness

For fixed n, take the finite set S of prime divisors of the numerator
of c and of 2·3·11·17. The above theorem says that the positive
squarefree representative of [r(a)] is supported inside S, so it lies
in a finite list. The degree-eight source polynomial factors exactly as

    r(a)=4 ∏(s_i·a(a+1)+t_i),
    (s_i,t_i)=(7446,661),(7446,1861),(29784,7445),(476544,119479).

All four ratios t_i/s_i are different and each discriminant
s_i(s_i−4t_i) is nonzero. Hence all eight geometric roots are distinct.
For each possible squareclass d, rational a with that class gives a
rational point on Y²=d r(X). Its smooth projective model has genus 3
(eight simple branch points; Riemann–Hurwitz). By
[Faltings' theorem](https://doi.org/10.1007/BF01388432) it has finitely
many rational points. Taking the finite union proves the assertion
for integer a. We do not require any uniform bound on d or n.
This argument needs the actual N,H,c identities: it does not follow
for independent slots or for n=n(a).

## Exact 5-adic constraint on both actual indices

The source elliptic curve is y²=x³−δx, δ=(3−√2)²; the globally
oriented half-generator R=(1+√2,2√2) doubles to P. The literal chart is
U_m=2y(mR)/(x(mR)²+δ), with x(mP)=1/U_m² for m≠0. The model has good
reduction at the inert prime 5, since 5∤2·Norm(δ)=2·49. Using exact
field arithmetic and the group law gives the following pairs of residue
coefficients of U_m (constant term, √2 coefficient modulo 125):

    m=1       2           3          4          5
    (113,104) (114,117)   (111,33)   (112,46)   (50,75).

Thus the first four mP have unit abscissa, whereas 5P reduces to the
identity and has formal parameter of valuation 2. Indeed over a good
integral model x of negative valuation is precisely the formal kernel
and v(−x/y)=−v(x)/2 in the kernel. In particular the reduction order of
P is exactly 5. All other m not divisible by 5 reduce to one of the
four nonzero multiples with unit abscissa. For nonzero m divisible by 5,
the formal group logarithm on valuation ≥2 is isometric and additive,
so v(formal parameter(mP))=2+v5(m/5). For this standard fact one may
integrate the integral invariant differential: its logarithm z+Σ a_j z^j/j
has v(a_j)≥0, and at v(z)≥2 all j≥2 terms have strictly greater valuation;
the formal logarithm linearizes multiplication. Using x=1/U_m² and
unramified residue degree 2 proves

    v5(Norm U_m)=0 if 5∤m, and 2+2v5(m) otherwise (m≠0).

The check lists all eight simple-prime classes modulo 25. For those a
the preceding k=1 result gives v5(H)≥2, v5(Q)≥0, so 5|h and
v5(c_n)≥15+v5(H). Taking m=n−1 then forces 5|(n−1) and the advertised
v5(n−1)≥v5(h)+8. For the illustrative legal n=−1, the literal
translated norm is c=Norm U_{−2}=Norm U_2=1405152/4905889, a 5-unit;
so all eight residue classes are impossible for any nonzero common h.
At a=0 this is an obstruction to the true scalar pole, irrespective
of projection to other chart rows. No complete source witness or
counterexample to its adaptive choices follows.

## Reproduction and pinned dependencies

Run python3 verify.py and compare to REPLAY.json. This is a paper proof
and exact rational check, not a Lean build. All source paths below have
prefix quartics/quartic-318-326/proof/experiments/ at commit
a0950ac7c24df6d336a196966fb790d6abd55e44. The indispensable maps and
quantifier order can be audited directly:

* forward-two-twist-realization-r2/ScalarForwardWitness318.lean SHA256
  115729a9f8748290186bb0396ed78dd0355ec3fd93ff8a7ffb02f653dad675a5
  (r,N,Q,W,poleInput) and ScalarActualInputs318.lean
  669eb03d31c5490f7278608a416e1e44ec64d10aa90c044c64c6636759e810f1
  (detector33, detector37).
* Same directory: PreparedIntegerSource318.lean
  e3ecec834054e138eb6cc64c92f0e431510c64a878803d689fa55a9fdf06c423
  (scalarB); NormalizedPolePoints318.lean
  410995ba113f37dfcb54261e61eb6b90fde58242a4fa0eed79282e99ad060542
  (two cubic equations); CoherentMultipleCharts318.lean
  01443a070ea295862a1c06111e8803651d6766afead3c3918797aa5718ba9bc9
  (chartU and chart_abscissa).
* forward-scalar-index-preparation-r2/ScalarTranslatedIndex318.lean
  5a19a15c2d3e7ad4dbdf805b470f9f70a8d9ab46851fa67d1a828174da8323db
  (shifted_chart and scalar_inverse_norm).
* forward-actual-ambient-primitive-lifts-r1/AllPrimePreparedFullSource318.lean
  a366cc42510e3ee84ee8b47f42e7e21113d47e44d0de2f33e31a8135bad6f65c
  (current_source: a precedes ∃J); its FixedArithmeticLabels318.lean
  675555b04e937103485cf11d3c296180711e4bef2f426edb8723bdda98383870,
  ScalarPreparedResidues318.lean
  be4d87be33f899ac34d05628486d58e7a471b4b3bfd96ebc1430311cb4276532,
  and PreparedAnchorLabels318.lean
  020eaad881c96b703b1304249f468550b784c69dbf181600696e7459a3d929d4
  (actual label/multiplier expressions).
