# Completeness assembly for the literal 318-variable source

## Status and source binding

This is a source-specific conditional proof of the direction

> For every integer input X, the final 318-variable source has rational witnesses.

It is not an unconditional validation of the construction and does not prove its converse. The two outstanding global arithmetic inputs are isolated below. In particular, no conclusion here discharges `sourceArithmetic` in the existing final Lean bridge.

Reviewed checkout: `e96c25a48a09034a52c3444cdd515c09720cd19d`. The exact source hashes and an exhaustive 288-row register are in `row-coverage.json`. The checked sources are the pinned `quartics/quartic-318-326/construction/318/build_source.cjs`, its raw, translated and sheared IR files, the current arithmetic supplement, and its two pinned manuscripts. All work in this directory is isolated from the checkout.

The source has 318 rational coordinates, including X, and 288 quadratic rows. There are 238 arithmetic/quotient rows and 50 structural rows. Every row is covered below; the executable coverage check rejects an unclassified row. Coverage itself is not a mathematical proof.

The inherited final completeness argument is present in Version 10, lines 19580–19698. The current supplement already supplies compressed-anchor, guard, branch and real-bound refinements. The main new connecting work here is (i) coherent fixed root signs before prime selection, (ii) the residue/trace argument for the actual left-deep chain with unsquared delta leaves, and (iii) exhaustive final-row assembly with the final 4/13, index-8 constants. These are connecting arguments, not a claim that the historical completeness proof was absent.

## 1. The hypotheses actually needed

Use K=Q(sqrt(2)), d=3−sqrt(2), D=d² and E: y²=x³−Dx. Put

- R0=(1+sqrt(2), 2sqrt(2));
- k=−1+(7/4)sqrt(2), m=39/8−(9/2)sqrt(2);
- P=2R0=(k²,km).

The displayed constants satisfy m²=k⁴−D. P is nontorsion; its 2-adic formal parameter has valuation 3/2, in the logarithm's torsion-free isometry region. This explicit fact suffices for completeness. The stronger assertions that E(K) has rank one or that 2E(K)=ZP are not needed in this direction.

The global hypotheses are:

**PP.** The precise simultaneous Gaussian-prime pattern and reduction-order theorem used in Version 10, including its separation refinement at lines 19639–19678. After fixing finitely many distinct forms u+c_j w², a finite avoidance modulus and arbitrary lower bounds, it supplies positive prime values, arbitrarily large u/w², arbitrary prescribed divisibility of w, the stated Gaussian ray classes, compatible doubling-image orders M−,M+, and separation of the selected primes from M+. The exact order/gcd conclusions used are displayed in Section 6 below. The companion `PRIME-PATTERN-AUDIT.md` traces the actual analytic argument and its published inputs. The finite order-separation/CRT consequences now have new kernel-checked proofs, but the full analytic prime theorem is not claimed as formally closed here.

**RC.** The restricted converse for E_l: y²=x(x−l)(x+3l), positive squarefree l≡11 mod12, together with the standard descent and forward analytic-rank-one results. Its consumed consequence is the preparation-zero pole existence statement in Brox v3 lines 2572–2599, derived from Version 10 `lem:original-seven-simultaneous-realization` and `lem:original-seven-parity-completeness` (lines 7780–7935). It is not the different `hyp:PC` predicate and does not invoke a converse for arbitrary elliptic curves. A separate audit is checking RC itself.

The remaining inputs are standard or explicit local facts: elliptic duplication/addition, formal groups at good unramified odd primes, finite local-index subgroups and continuity, the explicit reduction orders/ray calculation, compact real-group recurrence, and the three-witness semilocal characterization proved in Version 10 lines 10982–11004 using the quaternion algebra (2,3). The companion `ANCHOR-COMPLETENESS.md` now gives an independent direct Hasse–Minkowski proof for the exact consumed anchor, with every local place and its affine denominator checked. They are used with their stated hypotheses below. The global contact-height bound is not used anywhere in completeness.

## 2. Input, scalar point, odd Lucas labels and the anchor

Fix X∈Z. Set T=2X+1, beta=3723T² and

r=(beta−1)(beta−2401)(32beta+343)(2beta−1), c0=114444, a0=c0 r.

Then beta is odd, beta≥3723, and r>10. The elementary local calculations in the current supplement give:

- v2(r)=2 with odd unit 3 mod8;
- r≡2 mod3;
- r≡5 mod17.

Thus a0 is a square in Q2,Q3,Q17 and has valuations 4,2,2 there. The valuation 4 at 2 is the final source value; the earlier nested-input value 6 must not be substituted.

First choose a nonzero shared index h0, divisible by 64 and by the real component-group order specified below, so that H0=h0P is sufficiently deep at both places above every prime dividing a0. In particular, choose f(H0)/r arbitrarily small locally. Next choose a positive scalar index s, arbitrarily divisible, and R=sP sufficiently deep relative to H0. This makes

q0=N(uR)/(N(uH0)r^15), N0=N(1+f(H0)/r), W0=N0²+r q0²

satisfy W0≡1 at every prime dividing a0. Here uQ²=1/x(Q). Its square root exists because Q is a double, explicitly through the duplication chart in Section 3. The denominator N(uH0) is nonzero. Increasing the local divisibility of s makes N(uR) arbitrarily small at these finitely many primes.

Also require 6|s and v3(s)≥32767. At 3, P has reduction order 2 and v3(z(2P))=1. Since 3 is inert, this gives v3(N(uR))=2+2v3(s)≥65536. Therefore N(uR)/S is 3-integral for the actual S=3^65536. At 2, v2(N(uR))=3+2v2(s)≥0 and S is a unit. These are genuine finite divisibility requirements, even though enormous. No height theorem is required to impose them.

Set the scalar root label a=s+1. Require s large enough that a≥7. Define U0=0,U1=1,U(j+1)=a Uj−U(j−1), j=2(a−2), t=U(j+1), b=Uj/(a−2). Modulo a−2, Uj≡j, so b is integral. Since a is odd and a≡1 mod3, j≡1 mod3; the sequence mod2 has period 0,1,1. Hence t and b are positive odd integers, as are a and beta. The Lucas identity is

t²−a(a−2)tb+(a−2)²b²=1.

Use the four fixed root labels (nA,nS,nT,nZ)=(beta,a,t,b). None is zero. All root points Qi=niP are finite and nontorsion.

Once the root square roots hi in Section 3 are fixed, put C=product hi=C0+C1sqrt(2), nC=N(C). The exact 2-adic calculation gives v2(nC)=−12 because all four labels are odd. At 3, every odd multiple of P has unit abscissa, so nC is a 3-unit. Therefore

Aphysical=N(uR)+4096 S nC

satisfies Aphysical/S∈Z_(2)∩Z_(3). The direct local-global proof in `ANCHOR-COMPLETENESS.md` (equivalently the inherited semilocal theorem) gives rational u,v,w with

u²+6v²−2w²−3 Aphysical²+2S²=0.

This is exactly the last raw source row, including its sign and constant. It supplies all three anchor coordinates.

## 3. Coherent reciprocal charts and fixed scales

For a finite nontorsion point T=(x,y), define

u(T)=2y/(x²+D),
v(T)=(x⁴−6Dx²+D²)/(x²+D)².

Both denominators are nonzero at either real embedding because D>0. Extend by u(O)=0,v(O)=1. Duplication gives

v(T)²=1−D u(T)^4, and 2T=(1/u(T)², v(T)/u(T)³).

For a variable common index h choose the eight source charts from

TUi=[h ni]R0, TVi=[(h−1)ni]R0.

Their underlying points are Ui=[h ni]P and Vi=[(h−1)ni]P, with Ui−Vi=Qi. Thus the sixteen reciprocal structural rows hold exactly, with rational pairs for K-coordinates.

**Why the actual emitted square roots and scales can be fixed before h.** The source's reversed-root expression is

hi(h)=(u(TUi)v(TVi)+u(TVi)v(TUi))/(u(TVi)²−u(TUi)²).

The square-root addition identity gives hi(h)²=x(Qi). Regard hR0 as a variable point T on E. Both numerator and denominator are rational functions over K of T. The denominator is not identically zero: at T=O its value is f(−Qi)>0. Since K(E) is a field and x(Qi) has a fixed square root in K, the identity forces hi(h) to be one constant root throughout its domain, not a sign that may vary with h. Evaluation at T=O identifies that constant as

hi=−1/u([ni]R0).

This fixes C,nC and the literal source scales

A0=1, A1=(C0+nC)², A2=nC²

before any prime selection. All are positive. In fact |C_sigma|>d_sigma²>2 and |C0|<|nC|/2, so A1,A2>1. The proof does not choose these scales retrospectively after obtaining h.

The exact rational checker verifies this coherent-sign identity for nine nontrivial (ni,h) samples, plus three compressed anchors and three S−P scalar reconstructions. These checks support implementation; the rational-function argument above is the general proof.

## 4. Compressed H and scalar Kummer coordinates

Choose h≠0,1 later. Put H=hP, f=1/x(H), nH=N(u([h]R0)) and

w=(k f y(H)−m)/(k²+D f).

The denominator is positive at both real embeddings. The compressed relation

1−k² f(1+w²)−2m f w−D f²w²=0

follows from the elliptic equation, and nH²=N(f). Its reconstructed V0 is H−P, with f(V0)=f w². This fills the three compressed structural rows. Neither nH nor the log denominators A=m+(Df+k²)w and B=k²+mw+Dfw² vanish; the reconstruction/real-point identities in the supplement prove this, including w=0. Completeness deliberately chooses h≠1, so V0 is nonidentity and w≠0.

Let hS be the constant root of x(S), where S=aP, and jS=y(S)/hS. Since a≥7, x(S)≠x(P). Choose

rS=(k jS+hS m)/(hS²−k²).

Then rS²=x(S−P)=x(R), and

(hS rS)²−k²rS²−2m hS rS−k²hS²−D=0.

Thus both actual scalar Kummer rows hold on the intended minus branch S−P. Put scalar.rootNormR=N(rS) and scalar.normUR=1/N(rS)=N(uR). This inverse is legitimate. The source's normalized norm ratio is exactly N(uR)/(nH r^15), because its ri^16 numerator is divided by nH/r.

## 5. Uniform real region, guards, and local continuity

Let G be the closure of Z(P+,P−) in the product of the two real identity circles, G0 its identity component, and mG=|G/G0|. Each projection of G0 is surjective. Require 64mG|h0 and eventually 64mG|L.

Use the open region with sqrt(d_sigma f_sigma(H))>1/10 at both embeddings. Its Haar measure is at least

1−2/(10 sqrt(1−10^−4))>0.79998.

On it |N(uH)|>1/(100sqrt(7)), while |N(uR)|≤1/sqrt(7). Consequently the final scalar expression obeys

0<W=N(1+fH/r)²+r(N(uR)/(nH r^15))²
 ≤(1+1/r)^4+10000r^−29<2.

For each nonzero ni the stronger source guard is the coefficient-zero function

gi(H)=1/2 sum_sigma(f_sigma([ni](H−P))−f_sigma([ni]H)).

It is real analytic on G0 and at (O,O) equals a sum of two strictly positive values. Hence it is not identically zero, and its zero set has Haar measure zero. Remove all four such sets and the finite inherited multiplication/translation/quotient pole loci. Choose an open set with compact closure K0 inside the remainder. This gives uniform nonzero bounds for the four real-difference guards and uniform upper bounds for every test, before the prime theorem is invoked. If chart signs are viewed over the duplication cover rather than as functions of H alone, take the maximum over the finite chart choices; u,v themselves are bounded, and the remaining denominator exclusions depend on the underlying points. There is no independence assumption on the two real logarithms.

A potential ordering issue must be handled explicitly. The initial h0 was chosen before s and the root labels; one must not silently assert that every subsequently introduced quotient is defined at that h0. After the roots are fixed, if necessary replace h0 by a positive index in a sufficiently small finite-adic neighborhood of the original H0, still divisible by 64mG, and lying in the nonempty real open complement of the final pole loci. The required subgroup/progression is dense in G0. This preserves the already strict scalar local conditions. Only then fix the continuity modulus L. The fixed R and root labels do not change in this adjustment.

Enlarge L to preserve the scalar local conditions at every prime dividing a0 and boundedness of every comparison test at primes 2,3,17. Each condition is an open local condition on its actual nonzero denominator domain. For the coherent duplication charts, take continuity along the hR0 orbit, rather than silently treating a chosen square root as a single-valued function of H; enlarging L supplies this as well. L can retain divisibility by 64mG. The roots, scales, real bound and this L are now fixed.

## 6. Prime selection, final CRT and chart branches

For the five contacts Theta={0,−1/2,−1,1/2399,−32/407}, choose D0 such that D0² theta/Ar is integral for every r,theta. Set v=D0² w² and lambda=u/v. After merging repeated forms, the prime positions are

p_(r,theta)=u−(theta/Ar)v.

Require the primes to exceed 76176 and every prime factor of all fixed scale, contact-difference, root and continuity data. Impose the PP Gaussian rays pi≡9 mod16, pi≡1+3i mod7 and the stated avoidance rays. The order facts used are

M±=lcm_p(d±(p)/4), Pi=product of all distinct selected primes,
gcd(M−,M+)=1, gcd(M−,L)=16, gcd(M+,L)=1,
gcd(Pi,M+)=gcd(Pi,L)=1.

The last separation from M+ is the actual Version 10 separation lemma, not a consequence merely of pairwise gcd(M−,M+)=1. Its proof removes w<N^(1/3), uses w²=o(N), and then Hasse's bound to exclude equality between a selected prime and an opposite group order. Its required weighted-count premise remains part of PP's unresolved independent verification.

For the final source the old exponent 19 is unnecessary; exponent 3 suffices. Solve

h≡0 mod(Pi³ M−), h≡1 mod M+, h≡h0 mod L.

Pairwise compatibility follows from the displayed gcds and 16|h0. Every index and the step of the resulting progression are divisible by mG. Its closure in the real group is exactly G0, so its positive tail meets the interior of K0 at arbitrarily large h. Choose h>1 there.

At the chosen primary place over each selected p, H has formal depth at least 4 and Ui=[ni]H has at least that depth. At the opposite place V0=(h−1)P is formal. The required reciprocal v=+1 branch for Vi is supplied by the halving calculation: pi≡9 mod16 makes 2 a fourth power modp; p≡1 mod16 makes 2±sqrt(2) squares; hence epsilon=1+sqrt(2) is square at both K-places. The full 2-descent coordinates of R0 are epsilon,4,2/epsilon, all squares. Thus R0 lies in 2E(Fp), whose order is d±(p)/4. M+|(h−1) makes [ni(h−1)]R0 formal, so the duplication formula gives v(TVi)≡+1. This uses no incompatible extra p-power factor on h−1.

The fixed point P has unit reciprocal abscissa at selected primes. At the primary place V0 reduces to −P; at the opposite place H reduces to P. It follows that nH has valuation at least 4 and N(fV0) has valuation at least 2. These are the literal rational norm tests used in the final source.

The exact logarithm ratios for both groups equal ni. Primary z/full-log relative error has order at least 16. The alternate Padé(2,1) ratios have error at least 16, and the low J1 ratio at least 8, with the enforced plus branch. Thus every low test has order at least 4, and every high test at least 13. The Lucas residual has order at least 13 because its exact value on the integer labels is zero. Each linear conjugated delta leaf v−1 has valuation at least 4 at the successful place. These statements suffice for the weighted leaves below.

## 7. Actual detector chain and its pole hypotheses

For each fixed scale A=Ar set t=A lambda, delta=t−1 and

F(t)=product_(theta in Theta)(t−theta), e=(A delta)^5/F(t),
Rdet=1/(e delta)=F(t)/(A^5 delta^6), qm=e^(2m−1)/delta³ for m=1,4,13.

Choose lambda sufficiently large, as allowed by PP. Then t>1, F,delta,e and all weights are nonzero. The fourteen structural weight rows are filled by these rational values: e4OverDelta=e^4/delta, q4=e^7/delta³, q7=e^13/delta³, q13=e^25/delta³, and q1=e/delta³. The base detector's emitted q1=delta²/F is the same expression because A=1.

The exact source has sixteen leaves: twelve square leaves and four linear conjugated delta leaves. Starting from W0=1, its recurrence is W(j+1)=Wj²+q_(mj) leaf_j. At a selected contact prime p, v_p(Rdet)=1, v_p(e)=−1 and v_p(delta)=0, so every weight has negative odd valuation −(2m−1). Every nonsquared delta leaf has even valuation at either good place: this follows from (v−1)(v+1)=−D u^4, treating negative, zero and positive valuation of v−1, with p odd and D a unit. Zero leaves are allowed.

At either place above p, induction gives the stronger dichotomy

Wj has negative valuation, or Wj≡1 modp.

Indeed, a squared previous value has even valuation while a nonzero weighted leaf has odd valuation, so cancellation cannot occur. If the previous value is 1 modp, the added term is either small, preserving residue 1, or has negative valuation. If the previous value has negative valuation, the new minimum remains negative. A zero leaf simply squares the previous value.

This general induction, including zero leaves, is kernel-checked in `NormChainCompleteness.lean`. It is the missing bridge needed to apply the old trace argument to the final *chain*, rather than to an older product of factors. At the successful place all weighted leaves have positive valuation: square tests give −(2m−1)+2m≥1, and order-one linear delta leaves give −1+4≥3. Thus W≡1 there. At the other place W^−1 has residue 0 or 1. Consequently Tdet=Tr(W^−1) has residue 1 or 2, a unit because p is odd. The Lean file also checks the successful-place induction, reciprocal dichotomy, and their composition as `detector_trace_unit`, the exact local trace-unit implication.

Write W=w0+w1sqrt(2). Since Tdet=2w0/N(W), set

nW=N(W)/(2w0), Bdet=Rdet nW²=Rdet/Tdet².

The real choice below makes w0 nonzero, and W is already nonzero at contact places. These are the two actual structural trace/B rows. At a contact p, v_p(Bdet)=1. At every other prime, v_p(Rdet) is even: indeed

Rdet=product_theta(u−(theta/A)v)/(v^5 delta^6),

whose denominator is a square because v is a square. Each fixed detector has five distinct prime factors in the numerator; selected primes do not divide v or any fixed difference. Therefore the reduced denominator of Bdet is a square.

The Gaussian rays ensure each selected rational prime is square in Q2,Q3,Q17 (p≡1 mod8 and p≡1 mod3·17). The displayed product formula therefore makes Rdet, and hence Bdet, a local square at these three primes.

The final chain has the same real/small-prime limiting mechanism, checked with its actual weights. Uniformly on K0 as lambda tends to positive infinity,

e→A^5, qm=O(lambda^−3), W=1+O(lambda^−3),
Tdet=2+O(lambda^−3), Bdet~1/(4 A^6 lambda).

The four linear delta leaves may be negative, but they are uniformly bounded (each real delta lies in [−2,0]); this does not affect convergence. Thus w0≠0 and 0<Bdet<17 once the preselected lower bound for lambda is large enough.

At p=2,3,17 put nu=v_p(v), eta=v_p(A). For nu sufficiently large,

v_p(e)=5eta, v_p(qm)=3nu+(10m−8)eta,
v_p(Rdet)=nu−6eta.

The tests have fixed finite lower bounds by the choice of L. Hence every weighted leaf tends locally to zero with nu, the finite chain tends to 1, and v_p(Tdet)=v_p(2). Therefore

v_p(Bdet)=nu−6eta−2v_p(2).

Prescribe sufficient divisibility of w *before* PP to obtain v2(Bdet)≥3, v3(Bdet)≥1 and v17(Bdet)≥2 for all three detectors. These bounds and the real lower bound are fixed before invoking PP; no post-selection circular adjustment is used.

All hypotheses of preparation-zero pole existence now hold for each Bdet.

## 8. Scalar pole and the exact conic normalization

The final h lies in the local neighborhoods fixed by L. Thus its scalar W is a unit at every prime dividing a0. Its real position gives 0<W<2. Set

Bscalar=a0(W/(1+a0))².

Then 0<Bscalar<4/a0<17. At primes dividing a0 both W and 1+a0 are units, so Bscalar has nonnegative valuation there. At every other prime its valuation is even. Its reduced denominator is therefore a square. At 2,3,17 it is a local square with valuations 4,2,2, satisfying all preparation-zero thresholds. Also r>0, nH≠0, N(rS)≠0 and 1+a0>0, so every retained scalar quotient is defined.

Apply the RC-dependent preparation-zero existence theorem to all four B values. The source conics are not silently identified with a differently normalized predicate. If the original unnormalized two-conic witnesses are p_old,e_old,s_old,q_old, use

p=p_old, e=e_old/B, s=s_old/B, q=q_old/B.

All four B values are positive. Define Hpole=e(17−B), ss=s² and Tpole=(ss−Hpole)(ss+3Hpole). The exact resulting rows are

17p²−289B−578e+34Hpole+51e²−3eHpole=0,
17q²−B Tpole=0.

These are literally the builder's `firstConic` and `secondConic`, for both the three detectors and the scalar. The two old residuals are B and B³ times these residuals. Existing `ThreeHelperPoleNormalization.lean` proves the identities and existential equivalence, including B=0. Completeness uses only B>0, so no zero-fiber division occurs.

## 9. Completing every rational coordinate and row

Fill the 80 free coordinates with X, the eight reciprocal charts, the compressed H data, lambda, four pole witness quadruples, the three anchor witnesses, the fourteen conditional weight quotients, the six trace/B witnesses, and the scalar square-root pair. All lie in Q after writing K-elements in the basis 1,sqrt(2).

Fill the other 238 coordinates in dependency order with their literal exact assignments or quotients. Their denominators have now been verified:

- the four retained coefficient-zero root differences are bounded away from zero on K0;
- the rational-field denominators of the primary ratios correspond to nonzero v(Ui) and fixed k;
- for real reciprocal points delta∈[−2,0], so each J Padé denominator is ≥3/13;
- for the chosen V0, 0≤D f(V0)²≤1, so its G Padé denominator is ≥6/13 and numerator is ≥28/195;
- V0≠O, so its actual alternate log is nonzero and the four LP quotients are defined;
- lambda,F,delta,e and the weight denominators are nonzero by the positive large-lambda choice;
- w0 is nonzero by the uniform real limit W→1;
- r,nH,N(rS),1+c0r are nonzero as established above.

The 50 structural rows are exhausted by: 16 reciprocal equations, 3 compressed-anchor equations, 14 weight quotients, 6 trace/B quotients, 8 pole conics, 2 scalar Kummer equations and 1 semilocal anchor. The 238 remaining rows consist of 188 quadratic assignments, 16 rational quotient rows and 34 field quotient component rows. The source check verifies these counts directly and lists every row by its actual ID and name.

The raw anchor translation is invertible:

V=4v−2S, Wnew=4w−6S, U=4u−4S+3V−3Wnew.

The compiler certificate preserves the source projection. Its final fixed-parameter shear sends the old norm coordinates to parityNorm=4096nC and physicalA=N(uR)+4096SnC. The explicit inverses in the retained certificate recover the old coordinates. The independent finite checks already verify each row substitution; these are exact rational transformations, not new existence inputs. Consequently the rational raw witness gives a rational witness of every final sheared source row, and hence a zero of the final sum-of-squares quartic.

## 10. What is and is not finished

Completed here:

- A conditional source-specific assembly covering every raw/final row and every required quotient domain.
- A fixed-root-sign argument ensuring the literal final scales are fixed before prime selection.
- Explicit final CRT depth 3, plus-branch and local test-order checks.
- A kernel-checked completeness residue/trace module for the actual chain with linear delta leaves.
- Exact finite source accounting and rational identity smoke tests.
- A source-specific simultaneous-prime audit, with separate kernel-checked order-separation and three-modulus CRT lemmas.
- An elementary quadratic-reciprocity proof of the selected-ray fourth-power property and a kernel-checked explicit half of R0 in each residue field.
- A direct all-place local-global proof for the physical anchor, with kernel-checked local chart algebra, residue calculations and scaling.

Still not independently established here:

- PP, including the analytic weighted-pattern count used by the order-separation refinement.
- RC's positive-complex/central-calibration and other global analytic implications. The downstream two-twist/pole use has the correct restricted family, but is conditional on RC.
- A Lean theorem assembling the actual 318 source from formal versions of these global inputs. The new Lean modules prove the identified chain, order, CRT, branch and anchor substeps, not PP, RC or integer-to-source existence.

Thus this work narrows the completeness validation boundary and supplies real formal progress. It must not be described as an unconditional proof that every integer has a final rational witness until the two global inputs have been validated (or explicitly assumed in a theorem statement).
