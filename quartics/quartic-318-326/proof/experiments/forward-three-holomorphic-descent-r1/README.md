# Actual quotient and filled-source holomorphic germ comparison

Status: frozen. Thirty-one sources passed fresh strict replay and a private-inclusive
recursive audit of 568 declarations. Distinct non-author review is pending.

This packet proves local holomorphic-function comparison for the original
Gamma1(3) quotient and its actual simultaneous cusp filling. At every original
point, including elliptic points, holomorphicity of a function pulled back along
the original orbit projection is equivalent to ordinary holomorphicity of its
expression in the original T coordinate. At every added cusp, holomorphicity in
the actual selected source q disc is equivalent to holomorphicity in the ordinary
finite or reciprocal target sphere coordinate. These tests cover every point of
the actual compact filling and concern the same already proved compact map.

The source quotient condition is defined directly by the original orbit map,
not by transporting a target analytic structure. The critical-point descent
argument establishes the compatibility which simple transport would leave open.
The target charts here are explicit ordinary finite and reciprocal formulas.
This packet does not instantiate a bundled ChartedSpace/IsManifold structure or
identify OnePoint C with an arithmetic scheme analytification.

Twenty-six predecessor sources remain unchanged. Five new modules prove the
general descent argument, its actual-period application, the original quotient
germ criterion, the selected-cusp analytic inverse, and both full-filling germ
comparisons with their exact consumers.

## Exact application contract

1. Independent analytic germs and original source. QuotientHolomorphicAt u b
   means that u pulled back by the original orbit projection is analytic at
   every upper-half-plane representative of b, in the original complex source
   coordinate. This definition does not mention T or the target topology. The
   target is the independent punctured complex line, or the independent sphere
   with its explicit ordinary finite and reciprocal coordinate formulas.
2. Regular-point descent. For a holomorphic scalar f with nonzero derivative,
   the actual analytic local inverse is centered at f(z), returns z there, and
   satisfies the right-inverse relation on a genuine neighborhood. Composing
   the analytic pullback g composed with f with this inverse proves g analytic
   at f(z). No inverse-function hypothesis is applied at a critical point.
3. Critical-point descent and coverage. The derivative of a nonconstant
   analytic germ has isolated zeros. If it were zero on a neighborhood, the
   mean-value theorem on a contained connected ball would make f locally
   constant, contradicting the exact hypothesis. A small source neighborhood
   therefore has no critical points except possibly its center. Openness gives
   a full target neighborhood covered by that same source neighborhood. Every
   different target value has a regular preimage in it. Regular descent gives
   holomorphicity on the punctured target neighborhood; continuity at the
   center gives weak removable singularity. Openness itself supplies this
   continuity from pullback continuity, so no downstairs continuity is assumed.
4. Original period application. The original periodParameter is analytic on
   the actual upper half-plane and open by the previously proved complex open
   mapping argument and genuine nonconstant surjectivity. The original
   ofComplex partial homeomorphism transfers the source neighborhood filter
   exactly. Thus the general descent applies at every actual period point,
   including all critical points and elliptic representatives. Actual original
   surjectivity covers every nonzero target parameter.
5. Original quotient expression and consumer. parameterExpression u evaluates
   u at the inverse of the original global homeomorphism on nonzero t. Its
   arbitrary zero value is outside the target domain. Substitution of the
   original quotientParameter gives exactly u of the same quotient point, and
   substitution of periodParameter gives exactly u of the original orbit
   projection. These identities connect the analytic pullback criterion to
   QuotientHolomorphicAt with all representatives, not a selected generic lift.
6. Selected source cusp coordinates. The finite original End 3 indices and
   their selected integral representatives are unchanged. The proved selected
   source orders make 1/T at the infinity end and T at the zero end analytic
   of order one, with nonzero derivatives. Actual analytic local inverses give
   both inverse identities near zero. sphereCoordinate composed with the
   actual compact homeomorphism on the actual disc is exactly endCoordinate,
   including its origin. No derivative is inferred solely from topological
   bijectivity or a rational target ramification count.
7. Full-filling original germ comparison. An arbitrary function on the actual
   filling is expressed on the independent sphere using the same original
   compact homeomorphism. On the original image this expression agrees exactly
   with the original quotient function. Near each nonzero T point the ordinary
   finite expression equals parameterExpression as a germ, so the already
   proved original quotient criterion applies without losing exceptional
   original points or changing the source object.
8. Full-filling cusp germ comparison. sourceDisc is the actual selected disc
   map near zero; its values outside that disc are unused. Its target image is
   exactly inverseSphereChart composed with endCoordinate on the entire disc.
   Consequently the arbitrary function's source germ is the target chart germ
   composed with the actual order-one coordinate change. The regular descent
   lemma and analytic composition prove the two implications. Original-or-cusp
   exhaustion proves these comparisons cover every point of the actual compact
   filling, with both named cusp origins retained.
9. Verification and bounded conclusion. All thirty-one source modules are
   freshly checked serially with Lean 4.35.0 and kernel checking enabled.
   Recursive axiom collection includes private declarations and allows only
   propext, Classical.choice and Quot.sound. Twenty-six predecessor sources are
   byte-identical, with original baseline and predecessor contracts hash-bound.
   Distinct review is required. The result is exact local holomorphic-function
   germ comparison. A bundled manifold/atlas object, arithmetic projective-line
   analytification, integral PEL model, and the final height theorem are not
   asserted by this packet.

## Remaining boundary

The compact topology and original local holomorphic germ comparison are now
explicitly connected. Packaging these germs into a complex atlas and checking
its relation to an independently specified arithmetic analytification remains
separate. No PEL realization or FiveContact49Height/sourceArithmetic proof is
claimed.
