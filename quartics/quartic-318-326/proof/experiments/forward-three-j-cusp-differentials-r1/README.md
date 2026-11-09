# Cusp differentials and global ramification scheme

Status: uncompiled hosted-CI candidate. No local Lean build was run.

## Source and divisor

This is the degree-four self-map j(T)=(T+27)*(T+243)^3/T^3 of the genus-zero
projective line, identified with the compact level-three modular parameter
curve. It is not a map from a genus-four contact curve. The fibers above
infinity,0,1728 have degrees(3,1),(3,1),(2,2), separately summing to four.
Riemann-Hurwitz is-2=4*(-2)+6. The source ramification divisor and its degree-six
pushforward branch cycle remain distinct objects.

## What this stage constructs

The Kähler transitivity sequence proves a reusable complete relative-module
presentation from an absolute source differential frame and an actual polynomial
target coordinate. Localization frames then compute the exact g/f Jacobian.
Both original cusp source charts receive actual relative-module presentations
for1/j and exact scheme squares with the unchanged global map. The finite cusp
has a double Jacobian factor with nonzero cofactor1/3^17; infinity has value one.

The full principal Jacobian ideals agree with the finite degree-six equation
T^2*(T+243)^2*(T^2-486*T-19683) and the reciprocal equation
(1+243*S)^2*(1-486*S-19683*S^2). On the original entire Laurent intersection,
the equations differ by the proved unit T^6, and their extended ideals agree.
The literal Laurent relative Kähler module is now joined to the predecessor's
transported monic annihilator, with the exact j scalar action checked.

A genuine global closed subscheme is constructed from the monic degree-six
finite equation. Its Q-algebra has rank six; properness makes its immersion into
the original projective source closed. Its kernel is an actual global ideal
sheaf datum and its support stays in the finite chart. The Laurent and two cusp
presentation charts cover every source scheme prime.

## Precise remaining boundary

The global scheme, its finite equation, compatible overlap ideals and all local
relative-module presentations exist. The remaining globalization step is to
prove the formal restrictions of the global kernel ideal equal these chart
ideals and identify it with a globally defined relative-differential/Fitting
sheaf. This packet does not declare that last comparison by definition. General
quotient/PEL realization and the full318/326 arithmetic result remain separate.

Eighty-nine predecessor sources are unchanged. Two rational-pair evaluation
modules receive the narrow typed-projection/coercion repairs supported by the
latest hosted failure. Original failed source bytes and logs are preserved.

## Exact application contract

1. Full relative kernel from transitivity. Required: A Jacobian coefficient cannot be assumed to present the entire relative differential module. Constructed: FramedRelativeDifferentials318 uses the exact Kaehler transitivity sequence for R to R[X] to B and an actual absolute B-linear differential frame. Application: projection_kernel proves its full kernel is the span of the image of dX by tensor induction and the polynomial differential basis. relativeGenerator_kernel then identifies it with the principal Jacobian ideal, and quotientEquiv is an actual linear equivalence.

2. Actual source localization and target scalar map. Required: The source localization action on Q[T] must not be confused with the target-coordinate action on the same polynomial ring. Constructed: LocalizedRationalDifferentials318 constructs the source frame by the accepted localization frame theorem, differentiates the actual ratio g/f with a specified inverse, and defines a separate targetAlgebra taking target X to that ratio. Application: The entire relative module is presented by the image of g-prime*f minus g*f-prime times the inverse-square. The exact scalar tower is supplied for the target action, with the original source frame fixed independently.

3. Both actual source cusps and original scheme squares. Required: The monic Laurent algebra does not cover either omitted cusp; their own source/target charts are required. Constructed: ThreeJCuspDifferentialCharts318 supplies presentations on D(finiteNumerator) and D(reciprocalNumerator), both mapping to the reciprocal target coordinate1/j. Application: finite_scheme_square and infinity_scheme_square identify those coordinate maps with the original global j morphism. Explicit Wronskian factorizations give a square source-coordinate factor at the finite cusp and no such factor at infinity. Their actual rational evaluations are a nonzero finite cofactor1/3^17 and infinity Jacobian1.

4. Scheme ideals retain multiplicities. Required: Equality of zero sets or analytic orders cannot replace an equality of the principal differential ideals. Constructed: finite_jacobian_ideal and infinity_jacobian_ideal identify both full chart Jacobian ideals with extensions of the explicit degree-six finite equation and its reciprocal-chart equation. Application: The actual localization inverse is proved a unit and only its square and sign are removed. No radical or reduced-point quotient is substituted.

5. Full original overlap and degree-six transition. Required: Descent must hold on the actual entire scheme overlap with the correct scalar factor. Constructed: The homogeneous equation has degree six. overlap_equation proves finiteEquation(T)=T^6*infinityEquation(S) in the original Laurent intersection with T*S=1. Application: overlap_ideal identifies the images of the two polynomial principal ideals under the original finite and reciprocal inclusion ring maps. The factor T^6 is removed only because T is explicitly a unit on that whole intersection.

6. Literal Laurent differential join. Required: The transported monic annihilator from the predecessor must actually present the literal Laurent Kaehler module with the j action. Constructed: ThreeJLaurentDifferentialJoin318 constructs that presentation with the rational-coordinate frame method, proves actual_algebra equals the original jAlgebra, and compares the framed coefficient with the monic derivative image times S^3. Application: literal_coefficient_ideal removes that explicit unit and literalLaurentPresentation identifies the literal original relative differential module with the quotient by originalDifferentialIdeal. The prior transported-ideal boundary is thereby closed on the Laurent chart.

7. Actual global closed scheme and complete source coverage. Required: A proposed global ramification object must exist as a scheme with no spurious infinity support, and every differential chart must be accounted for. Constructed: ThreeJGlobalRamificationScheme318 constructs Spec of the monic degree-six ramification equation, proves its Q-rank is six, and embeds it into the original projective source as a proper closed immersion. Its kernel is a global IdealSheafData object. Application: finite_kernel retains the full defining ideal and support_in_finite_chart excludes an extra infinity component. every_source_point proves all-prime coverage by the Laurent and the two cusp differential charts, using original chart coverage and coprimality rather than complex-point exhaustion.

8. Exact hosted repair and immutable evidence. Required: Repair only the reported category projection failures and preserve the actual tested evidence. Constructed: The two symmetric rational-pair evaluation modules explicitly simplify AlgHom-to-RingHom evaluation and fully expose the typed aeval compositions before rewriting heval. Application: The denominator failures at lines22 and54 on commit c7d3bc3 are recorded with the exact available RESULT/log; the numerator receives the same source-supported projection fix. All other89 predecessors are byte-identical; no statement, map or mathematical hypothesis changes.

9. Genus, validation and remaining global comparison. Required: The genus-zero modular parameter map must remain distinct from genus-four contact curves, and local presentations must not be mislabeled as an already proved global Fitting-sheaf equality. Constructed: The actual map is degree4 P1 to P1. The source divisor has weights2,2,1,1 and degree6, and its pushforward has weights2,2,2. Six new sources plus two narrow repairs form97. Application: The global closed scheme and compatible chart ideals are now constructed, and literal relative modules are presented on a full source cover. Equality of the global kernel ideal with a globally defined relative-differential/Fitting sheaf, and formal restriction identification of that global ideal on every chart, remain separate. No local Lean, no integral characteristic3 extension, no PEL or full318/326 claim.

