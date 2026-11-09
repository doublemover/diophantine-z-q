# Finite elliptic orders and exact complex fibers of j

Status: uncompiled inactive hosted-CI candidate. Non-author source review and
hosted Lean checking remain pending. No local Lean build was run.

Three new modules prove the finite local-order formulas for the exact j action:
order1 at T=-27, order3 at T=-243, and order2 at every root of the original
quadratic D(T)=T^2-486T-19683 over j=1728. Neighborhood equalities transfer these
orders to the actual target chart of the genuine scheme-point action.

The finite target fiber equation is explicitly monic of degree4 for every
complex target value. Its root set, mapped through the original source chart,
is exactly the full actual fiber. Every complex-point fiber is finite, including
target infinity; the polynomial root multiset has cardinality at most4.

These concrete polynomial and complex-point results are not yet a scheme
finite-flatness theorem or a generic function-field degree theorem. They do not
alone establish a complete ramification divisor or the full318/326 proof.

## Exact application contract

1. Same rational and scheme maps. Required: The finite orders must concern the original J expression and the actual glued projective scheme action. Constructed: ThreeJEllipticOrders318 uses ThreeCompactParameter318.J and its original D quadratic; ThreeJActualFiniteOrders318 defines actualFiniteExpression by evaluationChart1 of literal mapPoints(chartPoint1 t). Application: actualFiniteExpression_eq establishes whole-neighborhood equality with J at every nonzero source coordinate, from exact finite formula and inverse-chart identities.

2. Both preimages over zero. Required: The simple and triply ramified roots of J must not be conflated. Constructed: order_at_neg27 gives order1 and order_at_neg243 gives order3, with exact zero_fiber classification for every nonzero t. Application: J_comp_order decomposes the actual factors. The vanishing linear factor has order1; all other factors and the nonzero denominator have order0. No assertion that every point over an elliptic value is ramified is made.

3. Every quadratic root over1728. Required: The order-two statement must quantify over every root of the exact elliptic quadratic and prove the derivative and denominator hypotheses. Constructed: root_ne_zero excludes t=0; root_deriv_ne_zero proves D derivative2t-486 cannot vanish at a D root; D_root_order is1. Application: If the derivative vanished then t=243, where D is nonzero by direct arithmetic. The original J_sub_1728 identity holds on a full neighborhood of every root and gives order2 after division by t cubed. No unproved root simplicity or chosen-root convention is assumed.

4. Orders of actual target coordinates. Required: Auxiliary scalar orders must be transferred to the genuine scheme-point action. Constructed: actual_order_neg27, actual_order_neg243 and actual_order_1728 concern actualFiniteExpression and its centered value1728. Application: Neighborhood equality with J is restricted to punctured neighborhoods for meromorphic-order congruence. actualFiniteExpression_analytic separately proves analyticity at every nonzero center. The exact scheme-valued zero and1728 fiber equivalences consume chartPoint injectivity.

5. Exact monic quartic fiber polynomial. Required: A degree certificate must bind to the actual cleared finite-fiber equation for every target value. Constructed: fiberPolynomial c is the explicit monic quartic with coefficients1,756-c,196830,19131876,387420489. fiberPolynomial_eval proves evaluation equals finiteN(t)-c*t^3. Application: monicity and natDegree4 are proved for every complex c, including exceptional targets. root_ne_zero excludes the denominator origin using the nonzero constant term; fiber_root_iff is exactly J(t)=c.

6. All genuine points in finite target fibers. Required: The fiber description must cover all source scheme points, not just an affine subset. Constructed: finite_fiber_eq identifies the complete mapPoints fiber over chartPoint1 c with the image of the actual quartic root set under chartPoint1. Application: finite_or_infinity exhausts every actual source point. Both source cusp origins map to target infinity and therefore cannot lie in this finite target fiber. Nonzero finite coordinates use the exact finite formula and injectivity of chartPoint1.

7. Root count and finite fibers. Required: Polynomial roots and scheme-point fibers need explicit finiteness proofs with nonzero polynomial hypotheses. Constructed: fiberPolynomial_monic supplies nonzero; finite_setOfPred_isRoot gives a finite root set; its chartPoint image is the exact finite fiber. card_roots gives total root multiset multiplicity at most4. Application: These are concrete complex-point and polynomial statements. They are not a scheme-finiteness, finite-flatness, generic function-field degree or algebraic multiplicity theorem, which remain separate.

8. Infinity target and global point-fiber coverage. Required: The target infinity fiber and every target point must also be covered. Constructed: infinity_fiber_subset restricts the fiber to the two actual source origins; all_point_fibers_finite splits every genuine target into finite or infinity. Application: For a nonzero finite source coordinate the image is in the finite target chart and cannot equal infinity; the two remaining origins form a finite set. This complements the full finite-target quartic root description without omitting target infinity.

9. Provenance, verification and remaining degree boundary. Required: New applications require hosted Lean and distinct review; source drafts must not upgrade predecessor status. Constructed: Three new modules extend58 unchanged sources from holomorphic-r3, inheriting its exact CI repairs. All61 sources are hashed with a recursive audit source. Application: Structural checks are not kernel validation. This packet does not yet prove existence/count of the quadratic roots, a full ramification divisor, generic degree4, scheme-finiteness, PEL/universal-family realization or the full318/326 theorem. Characteristic3 restrictions remain unchanged.

