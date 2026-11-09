# Maximality of the exact integral quaternion order

Construct actual maximality of the same perfect quaternion order among all module-finite Z-subrings, deriving reduced-invariant integrality rather than assuming it.

The same perfect period lattice is now proved finite over Z, rationally spanning the concrete division algebra, and maximal among all module-finite Z-subrings. The previous invariant-integrality hypotheses are discharged through an explicit commutative quadratic carrier for each nonscalar element, with scalar elements handled separately.

## Application obligations

1. **Same order and algebra.** Required: The PEL period lattice must not be replaced during the maximality proof. Constructed: All12 predecessors are byte-identical. The same B=(-210,5), μ, Rosati, perfect pairing and order basis remain fixed. Evidence: verification/SOURCE-COPIES.json.

2. **Noncommutative integrality boundary.** Required: Integral elements of a noncommutative ring need not be closed under arbitrary addition or multiplication. Constructed: Every use of IsIntegral.add and IsIntegral.mul is confined to a genuine commutative QuadraticAlgebra Q a b. Its star is an actual ring endomorphism. No commutative instance is assigned to the quaternion algebra. Evidence: PELQuadraticIntegralInvariants318.

3. **Exact quadratic carrier.** Required: A related quadratic field cannot supply invariants of the original element without comparison. Constructed: For the actual x, the carrier has relation ω²=−Nrd(x)+Trd(x)ω; the map sendsω to x and z to z.re+z.im*x. The original quaternion relation is checked coordinatewise. Evidence: PELQuaternionQuadraticCarrier318.relation; realization_value; realization_generator.

4. **Injectivity and exceptional scalar case.** Required: Integrality reflection requires injectivity, which fails for scalar x in a two-dimensional carrier. Constructed: For nonscalar x, one of its three actual imaginary coordinates is nonzero and proves the map injective. Scalar x is handled separately through the injective rational algebraMap; there is no nonscalarity assumption in the final invariant theorem. Evidence: PELQuaternionQuadraticCarrier318.realization_injective; PELQuaternionIntegralInvariants318.scalar_invariants.

5. **Integral reduced invariants.** Required: A finite overorder must supply both trace and norm integrality on its actual elements. Constructed: Integral x reflects to the literal quadratic generator. Conjugation, addition and multiplication there prove its trace and norm integral; injective rational scalar maps and integral closedness of Z inQ give integer values. These are exactly Trd(x),Nrd(x). Evidence: PELQuaternionIntegralInvariants318.invariants.

6. **Actual finite full lattice.** Required: A maximality statement should concern a genuine Z-order, not an arbitrary subring. Constructed: The exact Z⁴ additive equivalence gives Module.Finite Z order. A displayed rational linear combination of the same four basis elements spans every quaternion, with coefficients(r−j,i−5k,2j,10k). Evidence: PELMaximalIntegralOrder318.order_finite; rational_spanning.

7. **All module-finite overorders.** Required: Trace/norm caller premises must no longer hide the maximal-order conclusion. Constructed: For any Subring S containingO with Module.Finite Z S, every element is integral by the actual finite-module theorem and its subtype ring map. Derived invariant integrality feeds the previously proved exact trace-dual saturation, giving S=O. The stronger elementwise-integral version is also explicit. Evidence: PELMaximalIntegralOrder318.maximal_finite_subring; maximal_integral_subring.

8. **Remaining PEL joins.** Required: A maximal order and perfect lattice are not themselves a represented PEL abelian scheme or source identification. Constructed: Exact local ramification classification/reduced-discriminant identification, algebraization of the period family and its universal integral moduli realization, contact-to-moduli map and Hodge/KS comparison remain separate. The genus5 contact Jacobian is not identified with the dimension2 quaternionic surface. Evidence: README.md.

9. **Primary source and validation.** Required: Changed theorem applications need exact pinned APIs, independent review and hosted kernel acceptance. Constructed: Read pinned QuadraticAlgebra.Basic, IsIntegral.Basic, IntegralClosure.Algebra.Basic, IntegrallyClosed, Polynomial.RationalRoot and Finiteness.Basic. All12 predecessor source pins and new source/interface checks retained. No local Lean or whole-proof claim. Evidence: verification/primary-library-source-pins.json.

## Validation

Static closure, exact symbolic identities and audit-history controls are distinct from kernel acceptance. No local Lean compilation or build. Hosted recursive audit and independent bound acceptance pending. No full arithmetic theorem or algebraic PEL moduli construction is claimed.
