# Final 318 local soundness: source-specific bridge and proof boundary

This packet reviews the current 318 source, not the older 8/29 or 11/41
checkpoints. It makes concrete progress toward `sourceArithmetic`; it does not
prove that global theorem. No production source or polynomial has been changed.
All paths in the source references below are relative to
`quartics/quartic-318-326` in the checkout. `receipt.json` binds the files reviewed.

## 1. Results and exact boundary

**Kernel-checked results in this packet:**

* `SourcePole318.source_no_negative_odd` derives pole soundness directly from
  the current five quadratic pole/gate equations. It includes zero ordinate and
  auxiliary-witness branches. It assumes only that 3 and 17 are valuation units.
  It does not assume a restricted converse, elliptic rank theorem, or an inherited
  pole theorem.
* `RawSourcePole318.detector0_no_negative_odd`, `detector1_no_negative_odd`,
  `detector2_no_negative_odd`, and `scalar_no_negative_odd` consume the **literal
  `Raw318FinalReplay.stage0 S` constraints**, not an abstract equivalent source.
  They account for CSE's affine values H=17e-w and T=-3t.
* `RawReciprocal318` decodes all four actual alternate reciprocal charts and
  their conjugates, proving even valuation of the four literal unsquared delta
  leaves directly from `stage0`.
* `RawDetector318` proves the twelve literal square-leaf identities, all 48
  chain steps, all three complete fold identities, all terminal trace/B
  equations, and chain nonvanishing at odd-weight places. It handles the actual
  sixteen leaves and their actual CSE representations.
* `LocalSoundness318.source_detector_extract` combines actual field-valued
  chains, zero-leaf-safe parity recursion, the source trace equation, the source
  B equation, and the proved pole obstruction. It produces positive contact
  order and all leaf bounds at one common place.
* `contact_e_value`, `contact_R_odd`, and `weight_values` give the exact current
  weight values. The final weights are q1, q4, q13, with valuations -R, -7R,
  -25R. `leaf_spec_exists` derives the chain specification from intrinsic even
  valuation; the four linear delta leaves are not treated as global squares.
* `RawWeights318` decodes every literal five-helper weight equation and
  proves the contact valuation bridge for all three detectors.
* `ConcretePadic318` constructs actual embeddings at a supplied root
  rho²=2 in Q_p and its negative, pulls back the normalized p-adic valuations,
  identifies their restrictions with padicValRat, and proves the exact norm
  valuation sum. The existence of rho at a consumed prime is not assumed away.
* `SourceContact318.contact0_extract`, `contact1_extract`, and `contact2_extract`
  compose the full literal source, scales, weights, sixteen leaves, trace/B
  rows and pole obstruction. From finite v(A), odd v(F), and unit delta they
  derive R>0 and every leaf lower bound at one common place. Evenness of v(A)
  is derived from the actual square expressions, not an extra hypothesis.
* `SourcePadic318.contact0_at_padic` and its two companions realize the whole
  extraction at the actual ±rho embeddings, derive both discriminant unit
  hypotheses from p away from2,3,7, and require no free chain or pole predicate.
* `FiniteContact318.source_contact0`, `source_contact1`, and `source_contact2`
  start from a positive odd valuation of one actual factor t−c. Every rational
  difference among the five contacts and1 has checked numerator/denominator
  support in2·3·5·7·11·37·109·439·2399=9811490103030. This derives all other
  factor units, the delta unit and exact full F valuation before invoking the
  composed actual Q_p extraction. Its only arithmetic inputs are an actual
  split root, the selected contact, a finite scale valuation and good primes.
* `CompressedOrientation318` proves opposite H/V0 directions directly from
  the compression identities t²=f_H f_V and
  1=k²(f_H+f_V)+2mt+Dt². A positive value for either f forces the other to be
  a unit. The actual finite-contact wrappers derive both positive norm tests
  and all fixed coefficient units automatically.
* `RawLucasOrientation318` decodes the actual four primary reciprocal curves,
  four ratio equations and full Lucas residual. `ValuationLucasOrientation318`
  proves the Lucas residual is a unit in the wrong orientation, a contradiction.
* `SelectedContact318.source_contact0_selected` and its companions compose
  the entire literal-source contact/weight/chain/pole/orientation argument.
  At one actual split place every leaf bound holds and v(f_H)≥8; at the other
  place v(f_H)=0. These theorems contain no elliptic logarithm, formal reduction,
  group-label, prescribed orientation, or positive-R hypothesis.
* The doubled anchor identity, its logarithm-ratio algebra, relative-to-absolute
  error conversion, integrality transfer, and subtraction recovering a root
  label are proved with their exact hypotheses.

**Written mathematical application, conditional only on stated inherited
arithmetic inputs:** sections 2–8 below reconstruct the source-to-contact map,
the orientation, final logarithm precision, and scalar index divisibility.
They separate split and inert places and preserve the anchor's two-torsion.

**Not established by this packet:** split-root existence or inert exclusion at
arbitrary consumed contacts; the global rank/generator/squareclass theorem;
formalization of the completed local elliptic curve and its convergent formal
logarithm; final instantiation of the
semantic L/LP/Lucas coordinates; per-multiple elliptic norm formulas needed
by the separately proved 2-adic odd-anchor bridge; the global height
bound, restricted pole completeness, and integer witness construction.
Consequently no unconditional `sourceArithmetic` or integer-characterization
claim is made.

## 2. Freeze and historical attribution

The audited source is `construction/318/build_source.cjs`, together with the
pinned `construction/318/raw-ir.json.gz` and
`proof/318/Raw318FinalReplayData.lean`. The exact Lean consumer is
`proof/318/Current318FinalBridge.lean:2938–2946`.

Prior justification was found and read, separately from current incorporation:

* `docs/arithmetic.md:28–293`: actual compressed anchor, surviving T0-coset,
  and torsion-safe scalar proof.
* `docs/arithmetic.md:492–523`: rational norm tests and Lucas orientation,
  written at historical 11/41 precision. Section 6 below specializes the
  argument to the actual 4/13 source and does not import its old constants.
* `docs/arithmetic.md:620–647`: intrinsic parity of linear delta leaves,
  odd-weight noncancellation, and the zero-chain branch.
* `docs/arithmetic.md:1280–1342,1533–1588`: finite bad-prime inventory and
  complete small-prime logarithm-tail argument.
* `docs/sources/quartic_v10.tex:19600–19708`: two-ratio integrality transfer,
  final subtraction, and prior asymmetric-depth application.
* `degree8-original/arithmetic/parity/parity-justification.tex:15–39` in the
  repository: prior proof of the unguarded one-sided pole obstruction;
  `docs/sources/quartic_v10.tex:10556–10586`: preparation-zero specialization.

Thus the pole and local mechanisms are prior mathematical justifications now
partially connected and formalized. This is not a claim that they were newly
invented here or that every earlier audit checked them. The current application
is partly incorporated and partly still unformalized. Independent whole-proof
review has not occurred. A separate worker independently checked the mathematical
scope of `SourcePole318` and found its negative-odd obstruction and zero-witness
handling consistent; this was not an independent rebuild or global audit.

## 3. Contact parameter and exact weights

Use K=Q(sqrt(2)), d=3-sqrt(2), D=d². Exclude

    S_bad={2,3,5,7,11,13,17,37,41,73,109,359,439,2399,4801}.

For each of the three detectors, A is its nonzero rational-square scale,
t=A lambda, delta=t-1, and

    F(t)=t(t+1/2)(t+1)(t-1/2399)(t+32/407),
    e F(t)=(A delta)^5.

The base detector's fused equations q1 F=delta², e=q1 delta³ imply the same
identity. The common inverse equation makes lambda nonzero. Nonzero scales
come from the root-point reconstruction and its real argument, not merely from
an unconstrained coordinate name.

The change of variable phi(t)=2+1/t sends the five displayed finite detector
contacts respectively to infinity, 0, 1, 2401, -343/32. At a consumed good
contact p, exactly one displayed factor has positive odd valuation, all the
others are units, and delta is a unit. This is because all pairwise differences,
denominators, and differences from 1 have prime support in S_bad. A negative
valuation of t is not a contact: phi(t) reduces to 2, away from those five
points outside S_bad. A zero value of F is impossible from the source identity
and F(1)≠0 on nonzero scales.

Put a=v_p(A), f=v_p(F), and R=f-5a. Since A is a rational square, a is even,
so R is odd. **A need not be a local unit.** The source identity gives

    v_p(e)=-R,  v_p(e delta)=-R.

The five actual helper equations yield

    q1=e/delta³,
    q4=q1 e^6=e^7/delta³,
    q13=q1 e^24=e^25/delta³,

hence v(q_m)=-(2m-1)R for m=1,4,13. These facts are valid before knowing
R>0. Positivity of R comes from the pole/trace/chain argument, not from the
contact's positive F-valuation alone.

If t=1, the source permits degenerate auxiliary values. Set the effective
radical to 1 and use h(t)=0 directly. No division by delta or e is made in this
branch. Its finite five-contact support is entirely in S_bad.

## 4. The actual sixteen leaves and pole threshold

The source test indices, orders and leaves are:

    0:  nH,                         order 4,  leaf nH²
    1–4: u(UA),u(US),u(UT),u(UZ),   order 1,  square leaves
    5:  Norm(f(V0)),                order 1,  square leaf
    6–9: conjugate(v(Vi)-1),        order 1,  LINEAR leaves
    10: L_A-LP_A,                   order 4,  square leaf
    11–13: L_i-LP_i (S,T,Z),        order 13, square leaves
    14: L_A-beta,                   order 4,  square leaf
    15: Lucas(L_S,L_T,L_Z),         order 13, square leaf.

The chain order is 0,5,1,2,3,4,6,7,8,9,10,11,12,13,14,15, not numerical
test-index order. At every good place the reciprocal curve gives

    (v_i-1)(v_i+1)=-D u_i^4.

Every nonzero delta=v_i-1 has even valuation: if u_i has negative valuation,
v(delta)=2v(u_i); if u_i is integral, delta is integral and either has valuation
zero or v(delta)=4v(u_i). The zero delta case is allowed. Conjugation transports
this assertion to the opposite place. Existing `ValuationCurveParity` and
`ValuationEvenNormChain` prove these facts for actual additive valuations.

Write the actual recurrence as W0=1 and

    Wj=W(j-1)²+q_m * leaf_j.

Every nonzero right summand has odd valuation; every left square has even
valuation. Thus there is no cancellation, including with zero leaves, and no
Wj is zero at an odd contact. The exact finite valuation is the minimum of the
two valuations. In particular v(W16)≤0 at every place above the contact.

The literal terminal equations are

    2 w0 n = w0²-2w1²,
    B(e delta)=n²,

where W=w0+w1 sqrt(2). Equivalently n(W+conjugate W)=W conjugate W.
Since both factors W and conjugate W are nonzero, n and the trace are nonzero.
This derives the quotient domain at a consumed contact; it is not a global
assumption that w0≠0. The zero-chain/trace branch has no consumed contacts.

The exact pole rows, with H=e_pole(17-B), ss=s² and
T=(ss-H)(ss+3H), imply

    17 P²=B(17-e_pole)(17+3e_pole),
    17 q²=B T.

If k=v(B)<0 is odd, the first equation forces v(e_pole)=0: any nonzero
valuation, or e_pole=0, makes its right-hand side have finite odd valuation.
Then v(H)=k. In the second equation s² and H have different parity of valuation,
so both factors have the same finite valuation, and their product has even
valuation. Multiplication by B makes it odd, contradicting 17q². This also
covers s=0 and either ordinate zero. `SourcePole318` checks this argument.

Therefore v(B)=2v(n)+R is a positive odd integer. Since

    v(n)=v(W)+v(conjugate W)-v(W+conjugate W),
    v(W+conjugate W)≥min(v(W),v(conjugate W)),

at least one common place has 2v(W)+R>0. Backward chain induction now gives
R>0 and the prescribed order for every square-tested quantity. For a linear
delta leaf it gives half its valuation at least 1, hence delta has positive
valuation and selects the +1 reciprocal branch. No separate place is selected
for different leaves.

## 5. Actual points, labels, and torsion

The compressed source reconstructs H and V0 with H-V0=P. It imposes
nH²=Norm(f(H)), not that f(H) itself is a K-square. The inherited group and
squareclass theorem gives exactly

    H=hP+tau,   V0=(h-1)P+tau,
    h a nonzero integer,   tau in {O,T0}, T0=(0,0).

The T0 branch cannot be removed by a real-positivity assertion. All comparisons
must instead use

    [2h]Ui=[2m_i]H,
    [2(h-1)]Vi=[2(m_i-n_i)]V0,

where Ui=m_i P, Vi=(m_i-n_i)P and Qi=Ui-Vi=n_iP. These identities follow by
killing tau, not by asserting the generally false undoubled identity.

The reciprocal charts for Ui,Vi give square abscissas when finite, hence
membership in 2E(K), using the inherited squareclass theorem. Their u=0
branches represent O. The root real-difference guard excludes Ui=Vi, so each
root Qi is nonidentity, with n_i≠0. The root square-root expression and these
labels still require their full literal source decoder in Lean.

## 6. Norm tests and orientation at the final 4/13 orders

The selected place has v_p(nH)≥4 and v_p(Norm(f(V0)))≥1. The former norm is
nH². For a finite point, positive reciprocal-abscissa valuation is exactly
formal-group membership. Positivity of a norm makes at least one local
valuation positive.

H and V0 cannot both be formal at the same place because their difference P
has unit x and y at every p outside S_bad. Thus an inert consumed contact is
impossible. At a split contact they are formal at opposite places; at the
other place each reduces to ±P and its f is a unit. If V0=O globally, then H=P,
whose norm test is a unit: no detector contact is consumed. This exceptional
case is passed to the empty-radical height argument, never divided away.

Suppose the chain had selected the V0-formal place. There H reduces to P,
so z(H) is a unit. All four retained Ui membership tests make Ui formal or O,
hence every L_i=z(Ui)/z(H) is in the maximal ideal. The direct residual

    L_T²-L_S(L_S-2)L_T L_Z+(L_S-2)² L_Z²-1

would be -1 modulo p, contradicting its order 13. Therefore the selected place
is H-formal, with V0 formal at the opposite place. This uses the actual
retained Ui tests and makes no completeness-ray assumption in soundness.

Since f(H) is a unit at the opposite place, the selected norm identity gives
v(f(H))=2v_p(nH)≥8, and z(H) has depth at least 4. Every alternate Vi has the
+1 branch because its conjugated linear delta test has positive valuation at
the selected place.

## 7. Final local logarithm comparison

Let m_i be the signed Ui label. On the two formal groups the doubled identities
and nonzero anchor logarithms give the exact full-log ratios

    r_i=m_i/h,   r_i'=(m_i-n_i)/(h-1).

An active contact has V0≠O and V0 non-torsion, so h-1≠0. Because consecutive
integers cannot both be divisible by p, at least one ratio is p-integral.
The approximating ratios L_i and LP_i have the same valuations as r_i and r_i'
(the zero point gives zero on both sides). The cross-test has positive order,
so integrality transfers to both ratios.

In particular Ui has depth at least that of H, namely 4, when nonzero. The
primary z approximation has relative precision at least 4*4=16. At the opposite
place the actual high Padé(2,1) approximants have relative precision at least
16; low J1 for VA has at least 8, while its V0 denominator has at least 16.
All denominators are local units after extracting the leading z or -u factor.
The numerator and denominator domain checks are essential and are not supplied
by a quotient equation with a zero/zero right-hand side.

For every p>17, the entire series tail is controlled: the full logarithm's
coefficient at w^j has valuation at least -floor(log_p(4j+1)); for j≥4,
floor(log_p(4j+1))≤j-4. Thus at depth r≥1 the tail has relative valuation at least
16r and converges. The direct delta series has the same bound, after the
integral change of variables w=-2delta-delta². This uses the entire infinite
series argument in arithmetic.md, not merely the finite Padé remainder lemma.

Integral ratios turn these into absolute estimates. Combining with the
source cross-tests yields

    v(L_A-r_A), v(L_A-r_A')≥4,
    v(L_i-r_i), v(L_i-r_i')≥13 for i=S,T,Z.

Finally the exact identity

    L_i-n_i=h(L_i-r_i)-(h-1)(L_i-r_i')

recovers the root labels at the same order, since h and h-1 are integers.
Consequently every consumed detector prime divides the integer Lucas residual
in the root labels to order 13. It divides the reduced numerator of beta-n_A
to order 4. Local beta-integrality follows from its comparison with integral
L_A. No unnecessary division by h or h-1 occurs in this last step.

## 8. Scalar order 8, preserving the exact exponent 15

The literal scalar circuit has

    r=(beta-1)(beta-2401)(32beta+343)(2beta-1),
    Q=nR/(nH*r^15),
    N=Norm(1+f(H)/r), W=N²+rQ²,
    b=114444*r*(W/(1+114444*r))².

The exponent is **15**, since ri16 is divided by nH/r. The numerator nR is
Norm(uR), the reciprocal of the norm of the scalar square-root abscissa.
All actual input-denominator domains use the separate Q2 argument.

At every consumed scalar contact R=v_p(r)>0 is odd; the square input factor
3723 has support entirely in S_bad, and negative valuations of this degree-four
r are even. The normalizer is a unit. The now-proved source pole obstruction
and odd/even noncancellation give

    v_p(N)>-R/4,   v_p(Q)>-3R/4.

For each local place, f(H) has even valuation from the curve equation, so it
cannot tie the odd R. Thus

    v(1+f(H)/r)=min(0,v(f(H))-R)≤0.

The norm is the sum of these valuations with residue-degree weights. Its
lower bound forces v(f(H))>3R/4>0 at **every** place. H is formal there even
on its T0-coset.

Also v_p(nR/nH)>57R/4≥57/4, hence it is at least 15. Therefore
v_p(Norm(f(Rpoint)/f(H)))≥30. At some local place the ratio valuation is at
least 15; since both reciprocal abscissa valuations are even, it is at least
16. (At an inert place the residue-degree weight is 2; the same conclusion
holds.) Both points are formal there. Apply the logarithm to

    [2h]Rpoint=[2c]H.

Its isometry gives v_p(c/h)≥8. Since h is an integer, p^8 divides c. The scalar
point's signed label is whichever of ±a-1 the Kummer reconstruction supplies;
only ||a|-|c||≤1 is used later. This proof uses no sign of f(H) at real places.

## 9. Remaining proof obligations, without hiding them in one axiom

1. Finish split-root existence/inert exclusion at arbitrary consumed contacts,
   the map from the global radical to selected contacts, and source point/label/log-coordinate
   reconstruction in Lean. Actual split Q_p places, normalized norm/trace and
   rational weight specialization, all sixteen literal leaf identities, four
   delta parity applications, every chain recurrence and their complete
   common-place extraction are now kernel checked.
2. Formalize the actual local elliptic logarithm, its homomorphism and
   isometry, and identify it with the independently convergent H/G/J series.
   The separate padic-tail work now proves actual infinite H/J convergence
   and precision. Source residue orientation is proved here without formal
   group reduction. The checked algebraic log helpers do not assume the
   unresolved analytic/group identifications as conclusions.
3. Supply the inherited global group/squareclass theorem and actual raw
   point-label reconstruction. The separate height packet now proves the
   2-/3-adic all-multiple formulas by actual elliptic addition, doubling and
   triplication, and discharges them in the source anchor. Bounded independent
   reviews are recorded in anchor-peer-review and elliptic-two-review.
4. Supply the global modular/isogeny/height transfer and strict separation
   inequality; use the separate height work packet, with its stated premises.
5. Prove integer-input completeness, including the restricted converse and
   witness assembly. Local soundness neither needs nor proves that converse.

A passing compiler or axiom audit is not a substitute for any of these steps.
