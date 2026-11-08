# Independent review of completed torsion and splitting constructions

## Decision

**Bounded acceptance. No material mathematical defect or material scope overclaim found in the assigned constructions.** This is a non-author internal source review of the geometric author's completed work, not a new proof, external referee decision, full-project acceptance, or fresh local Lean replay.

The reviewed repository is `doublemover/diophantine-z-q` at `dea5d91b63e43d5f3ba9874c64463a0f28ff934b`. The exact files and receipt bindings are in BINDINGS.json. All 38 Lean files in the five assigned packets and the tangent precursor match their original producer receipt hashes. Supporting sources were read to check the particular maps used, not merely to count declarations.

The acceptance covers construction of the splitting extension; the actual tensor/evaluation algebra equivalences; the low-order equation families and field-point interpretation; the scalar-equivariant eight-label splitting and canonical torsor tensor map; the exact sign-invariant algebra; and the categorical equalizer on the nonvertical affine open. It does not identify any of these with a global multiplication kernel, an additive full-level marking, a modular moduli space, a discriminant-210 PEL object, or a geometric height realization.

## 1. Monic splitting is constructed, and the map is evaluation

`MonicRootEtale318.derivative_unit` uses the separability Bezout identity inside the actual quotient R[X]/(p). Its standard-etale presentation localizes at p'; since that image is a proved unit, `standardEquiv` really returns the original root algebra. Finite freeness comes from monicity, and positive degree over a nontrivial base gives a nonzero free algebra and faithful flatness.

`MonicEtaleSplitting318.exists_splitting` inducts on the degree. At degree zero, p=1 and S=R. At each positive degree it adjoins one actual root, divides by X-root, proves the remaining polynomial monic and separable with degree one less, and composes finite, etale and faithfully-flat structures. The roots and full factorization are outputs. They are not premises disguised as structure fields.

`SplitPolynomialAlgebra318` constructs the actual root-evaluation homomorphism. Separability of the product forces distinct linear factors pairwise coprime. Injectivity follows because every linear factor divides a representative with zero evaluations and the product then divides it. Surjectivity uses the polynomial-ideal CRT, not a point count. `MonogenicSplitEquiv318.baseChange` identifies the actual scalar extension with the mapped polynomial quotient. Its root and polynomial formulas are proved, and `splitEquiv_tmul_mk` gives precisely s tensor f(root) mapped to i ↦ s f(r_i).

Exact qualification: the constructed `Splitting` includes a nontrivial extension and therefore its construction assumes a nontrivial original ring. The generic README shorthand "every monic separable polynomial" is to be read with that theorem hypothesis; this review does not extend its quantifier to the zero ring. The positive-degree hypothesis belongs to faithful flatness of a single root algebra; the degree-zero splitting itself is separately handled.

## 2. The literal rank-three and rank-eight families

The cubic is literally x^3+Ax+B. Its displayed Bezout identity supplies separability when Δ=-16(4A^3+27B^2) is a unit. Its coordinate map sends the curve coordinates to root and zero, is surjective, and has a unique-factorization property for y=0 over arbitrary coefficient algebras. The order-two proof uses the genuine Mathlib elliptic-point group law and proves both root-to-order-two and exact-order-two-to-y=0.

For order three, the literal polynomial is ψ3=3x^4+6Ax^2+12Bx-A^2. With 3 invertible, the monic polynomial is ψ3/3. Its derivative and Bezout identity with the cubic are proved universally. Unit Δ implies both 2 is a unit and 4A^3+27B^2 is a unit; these are used, not omitted. The cubic value in the quartic quotient is a unit. Adjoining y with y² equal to that value is therefore a rank-two finite-etale faithfully-flat extension. Transitivity gives the actual rank-eight algebra; ranks require nontriviality. Neither a square root in the base nor an algebraically closed field is assumed.

`ThreeTorsionFunctor318.solutionEquiv` is an actual equivalence between algebra maps out of that iterated quotient and the two coordinate equations, for every commutative R-algebra S, including nonreduced S. `toHom` is a pair of quotient lifts. Its two coordinate formulas and generation by x,y prove both inverse laws. Division by 3 is justified after every base extension by the mapped unit.

`ThreeTorsionPoints318.root_iff_double_neg` proves ψ3(x)=0 iff P+P=-P by the actual tangent slope and Mathlib addition formulas. The unit-discriminant Bezout calculation rules out y=0 on ψ3; 2y is then invertible over the field. Conversely, P+P=-P rules out the vertical branch. The nonidentity condition and primality of 3 give exact order three, rather than merely order dividing three. `ThreeTorsionFieldPoints318` transports the coefficients and discriminant through the actual algebra map R→K and uses smoothness to obtain the actual nonsingular point. Its result applies to all field coefficient algebras with the specified map, not merely geometric points over an algebraic closure.

The later `ThreeTorsionOrderEquiv318` packages this into an equivalence with the exact-order-three subtype, explicitly excluding the identity. That packaging belongs to the present reviewer's earlier analytic lane: it was read as a consuming interface, and is **not** being independently approved by its own author here.

## 3. Eight-point product splitting and scalar action

`ThreeTorsionSplitData318` first constructs the quartic splitting ring S. Each cubic value at an x-root is the image of the already proved cubic unit. `FourUnitCover318` adjoins square roots of all four units by an actual tensor of four quadratic root algebras. This extension T is finite, etale and faithfully flat over S and hence over R. It is proved nontrivial. Roots, their equations and units are outputs.

`ThreeTorsionSplitEval318.evaluation` is the map from T tensor_R B to functions on Fin 4 × Bool given by evaluation at (x_i,±y_i). Its exact pure-tensor formula is recorded. For arbitrary target values f(i,+),f(i,-), its surjectivity proof constructs coefficient functions

- a_i=(f(i,+)+f(i,-))/2,
- b_i=(f(i,+)-f(i,-))/(2y_i),

lifts a and b through the actual quartic evaluation inverse, and returns a(x)+b(x)y. Both signs are checked. Injectivity is then obtained from the surjective linear map between the finite free modules of equal rank eight using Mathlib's Orzech-property theorem for commutative rings. It is not an invalid dimension argument restricted to fields, nor an inference from eight geometric points.

The eight primitive labels are a finite explicit bijection, with the sign flip matched to scalar -1. At level three the unit group is precisely {1,-1}; `diamond_mul` proves its action law and `equivariant` proves the actual evaluation compatibility. This proves scalar/diamond equivariance only. The four representative labels are not asserted to give a group-homomorphic or symplectic basis of E[3]. The README explicitly preserves that distinction.

`ThreeTorsionTorsor318.torsorEquiv` is the canonical map over the **actual invariant algebra**, b tensor c ↦ (g ↦ b ρ(g)c), for every subgroup H of (Z/3Z)^*. The generic predecessor was checked through `InvariantBaseChange318`, `InvariantRegularSplit318` and `FaithfullyFlatTorsor318`: finite simultaneous fixed equations commute with flat base change; the chosen orbit representatives give a regular split cover over the invariant base; the exact canonical map commutes with scalar extension; faithful flatness descends bijectivity of that map. This is not a supplied torsor isomorphism or a comparison over the wrong base.

## 4. The sign quotient is exactly the x algebra

`ThreeTorsionSignQuotient318.xToFixed` is the original coefficient inclusion XRing→B, restricted to full diamond invariants. Every element of B is a+by. Negation fixes a and changes the sign of by. The actual units 2 and y imply that a fixed element lies in the image of XRing. The original coefficient inclusion is injective by the positive-degree monic quadratic quotient, and is therefore an algebra equivalence onto the full fixed algebra. `signQuotientEquiv_val` preserves that exact inclusion. Rank four is a consequence, not the identification argument.

The full rank-eight family on a chosen elliptic curve is not conflated with the rank-four sign quotient. The analytic/coarse source uses the latter. The sign-quotient README is explicit that this algebraic statement alone does not establish analytic descent or a global modular-source comparison.

## 5. The categorical equalizer includes nilpotent and nonaffine tests

Let C=R[x,y]/(y²-x³-Ax-B) and U=C[(2y)^-1]. `NonverticalDoubling318` defines two algebra maps C→U: the actual tangent-diagonal formula and actual affine negation. The tangent precursor defines λ=(3x²+A)/(2y), with output x'=λ²-2x and y'=λ(x-x')-y, and proves the output is on the curve. The general pair formula uses y1+y2 as denominator and does not cancel x2-x1, so its restriction to the diagonal is legitimate.

`ThreeTorsionTangentCriterion318` proves the identity

(2y)²(λ²-3x)=(λ(2y)-(3x²+A))(λ(2y)+(3x²+A))-ψ3(x)-12x(y²-(x³+Ax+B)).

Using the curve and slope equations and unit 2y gives ψ3=0 iff the actual doubling coordinates equal (x,-y). This proof works over arbitrary commutative rings, not merely reduced rings or fields. Normalization by 3 and the x,y universal property yield unique factorization through B.

The map U→B exists because 2y is a proved unit in B, and its composite C→U→B is exactly the original curve coordinate quotient. Naturality of the localized diagonal is proved. Thus every R-algebra cofork factors uniquely, giving the actual coequalizer in CommAlgCat R.

The next step is essential and present: `ThreeTorsionRingCoequalizer318.ring_existsUnique` handles an arbitrary ring map k:U→S, induces the R-algebra structure on S via k, and proves uniqueness using surjectivity of U→B. Therefore the same quotient is a coequalizer in **all commutative rings**, not just R-algebras. Passing to opposites reverses the arrows. `ThreeTorsionEqualizerScheme318.isLimit` then applies the actual Spec functor, which preserves limits by the pinned Γ-Spec adjunction. Its `universal` quantifies over every Scheme X, without affine or reduced hypotheses. The inclusion composes to the original coordinate inclusion, and its closed-immersion theorem uses the proved surjective coordinate map.

This is a categorical equalizer inside the nonvertical affine open. It does **not** supply a completed relative multiplication-by-three morphism or identify the complement of the identity in its kernel. Those require the global group law and an open-locus reduction. Neither is inferred from the field-point theorem or the categorical equalizer. Both the packet README and the main progress README state this boundary correctly.

## 6. Actual consumers, historical disposition and remaining scope

The cubic and quartic algebra constructions are specialized to `OpenJModel318.integralModel N` through the literal coefficient maps. Here N is a nonzero localization parameter, not a variable torsion order. The orders remain respectively two and three. `PrimitiveTwoModel318` and `PrimitiveThreeModel318` supply their own splitting/action to `PrimitivePointedModel318.component`; the field-valued point β is still an explicit input. The quotient point is β restricted to the actual fixed algebra. The named pointed-normalization predecessor preserves that point and provides the proper model. This review checks the parameter/map connection, not every independent proper-normalization theorem in that predecessor chain.

The later exact-order field-point interface and sign-fixed interface feed the analytic comparisons. They do not turn the arbitrary eight scalar-compatible labels into additive level data. No statement in the assigned sources constructs the D210 universal abelian surface, identifies a PEL fiber, supplies the source's degree-576 field, or discharges `RefinedGeometricRealization`/`FiveContact49Height`.

Historical classification: **prior justification found and independently read** for the assigned algebraic and categorical claims. Old receipt remaining-input lists such as the absence of eight-point splitting or a closed immersion are historical and explicitly superseded by later packets. The main README already says such lists are not current-global status. No repair is required by this review. Incorporation status: the mathematical sources and bounded claims are already in the pinned progress checkpoint; this new acceptance packet is pending central integration and does not amend the manuscript.

No blocking finding is raised. Nonblocking precision: retain nontrivial-base assumptions for ranks/splitting, the invertibility of 3 and unit Δ, the supplied β in pointed components, scalar-only marking, and the nonvertical domain in any summary. Removing those qualifications would exceed this acceptance.

## Validation and independence

The reviewer is `/root/restart_modular_curve`, not the author `/root/restart_geometric_model` of the assigned packets. Runtime model/version metadata was not exposed and is not guessed. The review used direct Lean source and predecessor-map inspection, exact receipt hashing, explicit map/inverse reasoning, and README/consumer comparison. No new Lean sources, shared repository files, historical verdicts, or manuscript text were edited. No local compile was run and no fresh local kernel check is claimed. No additional stress test is needed for this bounded decision.

Checkpoint coordination reports success of hosted run 42450454824 at `0e5ff6ec3af901673ae4cf312329f3da0e503cf4`, with full audit job 128640564405. The reviewer independently checked by git diff that all Lean source files under the progress directory are unchanged between that commit and the reviewed `dea5d91`. The CI conclusion itself is attributed to checkpoint's retrieval, not claimed as independently fetched here. The older producer replay/recursive audit evidence remains separate from this semantic review. No full-project correctness or unconditional arithmetic theorem follows from either.

CI link: https://github.com/doublemover/diophantine-z-q/actions/runs/42450454824
