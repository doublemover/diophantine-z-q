# Labeled contact function-field reconstruction

Eight new Lean sources, no copied or modified accepted source. Structural checks
are not proof validation. No local Lean build has been run; hosted elaboration
and fresh independent acceptance are pending.

The original candidate is a field L with its specified Q(t)-algebra and actual
degree16. Geometry must supply FOUR ACTUAL quadratic character functions y_i,
their nonzero squares b_i in Q(t), and branch parity at EVERY prime polynomial.
The input is not an abstract model chosen merely to have degree16.

FourRootEvaluation318 constructs the literal nested tensor evaluation on the
original four polynomial root quotients, checks all four generators, proves
hom extensionality and actual supplied-action equivariance.
ComplementRootReconstruction318 recovers individual radicals by
x_i = complementaryProduct(y,i) / allProduct(a).
Complementing twice computes the denominator exactly. It proves x_i²=a_i and
complementaryProduct(x,i)=y_i EXACTLY, including signs. Independence of the old
four contact squareclasses makes this actual hom injective. Equal degree16
then makes the SAME hom surjective; no unrelated vector-space map replaces it.
ComplementRootAction318 computes the full-product square factor in the inverse
character transformation. A supplied geometric action intertwines the OLD
root-sign map on every element only after its complementary-root formulas are
proved. LabeledContactFieldReconstruction318 specializes to the original
contacts0,32,76832,-343 and retains arbitrary nonzero rational twists. Existing
published rational coefficient scalings, not equal j, identify the fixed old
arithmetic twist when actually supplied.

SquareclassRadicalNormalization318 removes arbitrary square factors from the
actual four functions in L. The resulting isomorphism preserves each old
function by the explicit identity e(characterGenerator_i)*u_i=y_i, with every
u_i a nonzero element of the ORIGINAL Q(t), not an extension of constants.

PolynomialEvenSquare318 generalizes the exact normalized-factor proof read in
accepted SquareFactorization318 to polynomials over a field. Even multiplicity
at ALL prime polynomials gives a square times an actual polynomial unit, which
is proved to be a nonzero scalar. RationalFunctionEvenSquare318 uses the OLD
canonical coprime RatFunc numerator/denominator. Coprimality separates the two
multiplicity parities, giving x=C(c)*z² globally. Prime polynomials of degree>1
are included; no unproved assumption that all branch points are rational is
used to omit them. The global identity includes infinity; no affine-only
isomorphism is substituted for it.

ContactDivisorFieldReconstruction318 applies this to b_i/P_i, where P_i is the
original product of the THREE contacts complementary to i. The four resulting
scalar twists d_i are turned into consistent individual twists by
c_i = complementaryProduct(d,i). The extra allProduct(d)² factor is retained
and absorbed by the explicit square scaling. The terminal reconstruct theorem
concludes an actual original contact-field isomorphism preserving all four
supplied functions, from actual roots, degree16 and ALL-prime branch parity.

## Historical evidence and exact remaining geometric boundary

Read quartic_v10.tex lines6861–6937 and the actual argument in
progress/receipts/fiber-field-bridge/FIBER-PRODUCER.md sections1–2, rather than
inferring a source theorem from its title. The historical application traces
Gonzalez–Rotger Theorem4.2/Table2 and the genus formula to five labeled branch
points, and exact cross-ratio computation to the contact coordinates. This is
prior source/application justification, NOT a Lean construction of the PEL
curve, its W action, quotient map, local orders or full branch divisor.

The published X/<w_m> quotients have degree2. The original complementary
character quotients in this packet have degree8. Their rational Jacobian
comparison through the residual full2torsion quotient must still be supplied;
one must not identify them merely because both have genus1 or the same j.
Actual rational short-Weierstrass scalings remain an explicit input to the
fixed-twist endpoint. A function-field isomorphism is not silently upgraded to
an isomorphism of the original proper smooth curves.

The intended target is the GENUS5 contact curve versus maximal-level Shimura
curve X of discriminant210. The dimension2 quaternionic abelian surface is a
UNIVERSAL FAMILY FIBER over X, not the contact Jacobian, which has dimension5.
This packet asserts no represented Jacobian, PEL moduli construction, universal
family, polarization, or global isogeny. The already separate first-order
Picard-kernel correspondence remains available for later geometric consumers.

Revision2 opens BigOperators explicitly in all eight sources after independent
preflight. All statements and proofs are unchanged; frozen r1 preserved.
