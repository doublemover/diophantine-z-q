# Exact original level-three arithmetic moduli map

Status: uncompiled hosted-CI candidate. Structural checks and non-author source
review are distinct from kernel validation. No local Lean build was run.

This packet constructs the actual arithmetic scheme comparison on the original
rational parameter open. It uses the original Laurent chart, localizes at the
pullback of j(j-1728), and constructs the base map into the original integral
open j-base. The literal elliptic family is pulled back along this actual map.
The explicit normalized torsion x coordinate satisfies the original division
equation inside the source ring, giving an AdjoinRoot map into the original
full diamond-fixed algebra. Both the arithmetic base square and the original
global finite projective j square commute as equalities of scheme morphisms.

Every evaluation of this constructed scheme map equals the pre-existing
arithmetic complexPoint, with both j and the actual marked-point x preserved.
The resulting arithmetic point comparison is bijective on its full old domain.
The same source scheme points are exactly the restriction of the independently
constructed compact analytic/projective comparison. The original period1/3
and its actual scheme point are retained, without arbitrary division-root labels.

This does not infer a scheme isomorphism from bijectivity on complex points.
The arithmetic open-map isomorphism, actual projective generic-stalk degree,
global universal-family/PEL extension and full318/326 theorem remain separate.
The rational construction makes no false claim of extending through3 or filling
the old affine x model at the exceptional j values.

## Exact application contract

1. Actual source open and base scope. Required: The moduli bridge must use the original projective parameter source and the exact old arithmetic base, without extending the integral model through3 or exceptional j fibers. Constructed: Ring is the localization of the original Laurent ring at jLaurent*(jLaurent-1728); its Spec embedding is the original Laurent inclusion followed by the original source projective embedding. Application: The source range is exactly the corresponding basicOpen in the Laurent scheme. The construction is rational and retains all original excluded values; no full Z-model or elliptic-fiber extension of the old affine x chart is claimed.

2. Constructed arithmetic base change. Required: A pointwise j formula does not define a family map without proving denominator invertibility. Constructed: The original source TS=1 identity proves j-1728=D(T)^2*S^3. Localizing makes j,j-1728 and D units. The actual localization lift defines baseMap from OpenJModel318.Base3 into Ring. Application: The literal original elliptic family is mapped along this constructed baseMap, remains elliptic, and its genuine Weierstrass j equals the same source j. Rational inversion of18 is justified through the Q-algebra map; no inverse is assumed at characteristic3.

3. Original division equation in the source ring. Required: The actual third-division algebra requires its defining polynomial to vanish inside the source ring, not merely at analytic points. Constructed: x=3(T+27)(T+243)/D and k=N(T)/D^2 satisfy x^4-6kx^2-8kx-3k^2=0 from D*v=1 and a polynomial identity. base_A/base_B identify the original family coefficients with -3k/-2k. Application: The original division polynomial vanishes by this identity. Its exact scalar relation with the monic division polynomial, together with invertibility of3, proves the AdjoinRoot lift condition.

4. Actual diamond-fixed algebra consumer. Required: A four-point count or arbitrary labeling does not identify the original primitive-three quotient. Constructed: xMap is the actual AdjoinRoot.lift into Ring. fixedMap is its composition with the inverse of the original ThreeTorsionSignQuotient318.signQuotientEquiv. Application: The map consumes LiteralThreeXComparison318.Fixed3 unchanged and preserves its original base j and xGenerator exactly. This is the full original diamond-fixed algebra, not an unnamed isomorphic four-dimensional algebra.

5. Exact scheme morphism and j square. Required: A coordinate map must induce a morphism of the actual schemes and agree with the global finite j morphism. Constructed: arithmeticMap is literal Spec.map fixedMap; arithmetic_base_square is equality with the actual base map. global_j_square identifies the projective embedding followed by ThreeProjectiveJMap318.map with rationalJ followed by original chart1. Application: The global square uses the whole Laurent scheme square and equality of polynomial ring maps, not dense-open complex-point inference. The global proper/quasifinite finiteness theorem remains for the same original projective map.

6. All admissible evaluations and x marker. Required: The new arithmetic map must agree with the old comparison at every point of its full domain, including the chosen actual marked-point coordinate. Constructed: evaluation is two successive localization lifts at every ParameterOpen point. Exact evaluations of T,S,j,D,v,x give J(T),X(T). Application: ModularArithmeticCoordinates318.hom_ext uses both original j and x generators to identify evaluation composed with fixedMap with complexPoint3(sourceParameter3.symm T). This does not infer equality from matching j alone.

7. Whole-domain arithmetic point coverage. Required: The comparison must neither omit branches nor replace source points with arbitrary labels. Constructed: arithmetic_evaluation_bijective composes the existing actual complexPoint injectivity/surjectivity with the explicitly inverse original sourceParameter. Application: All points of the original fixed algebra over C are covered exactly once by the constructed arithmetic scheme map evaluations. This point theorem is not used as an unproved scheme-isomorphism criterion.

8. Compact analytic source and actual period compatibility. Required: The moduli interface must consume the existing compact analytic comparison, not a fresh source with the same j invariant. Constructed: sourcePoint_compact identifies the constructed source scheme point with compactPointHomeomorph(original q). sourcePoint_arithmetic gives the original arithmetic schemePoint, and sourcePoint_period retains the actual fixedPoint from period1/3. Application: parameterPoint_embedding is equality of actual evaluation scheme morphisms. The sourceParameter restriction theorem retains original x and actual quotient points. sourcePoint_global_j then uses the same compact global j map; inherited full cusp/elliptic holomorphy and local-order results remain unchanged.

9. Verification and remaining scope. Required: New localization, root-lift and scheme-comparison applications need source review and hosted Lean before proof acceptance. Constructed: Five new modules extend the frozen66-source finite-j packet unchanged. Algebraic polynomial identity was independently checked by symbolic expansion as a diagnostic only. Application: No Lean ran locally. The new arithmetic scheme map is not yet shown to be an isomorphism, nor is global universal-family/PEL realization or projective generic-stalk degree supplied. The map and exact all-point comparison are substantive constructed data; full318/326 remains open.

