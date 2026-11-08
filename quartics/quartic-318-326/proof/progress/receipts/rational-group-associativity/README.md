# Actual associativity for every nonsingular rational short model

RationalGroupAssociativity318.associative (A B : Q) (hD : IsUnit (-16*(4*A^3+27*B^2))) proves equality of the original completed leftAssociate and rightAssociate Scheme morphisms on their exact left-associated relative triple. There is no OpenJ coefficient-ratio premise, nonzero-A/nonzero-B restriction, unconstructed specialization, or twist.

The proof constructs the actual rational short Weierstrass model over each field extension and matches the exact finite/completed Scheme point coordinates with Mathlib’s point type. The original chord, tangent and both infinity-output charts are individually matched to genuine point addition, then the original whole finite and whole completed additions. The actual rational triple is proved reduced using the existing geometric-integrality/properness results. Only then are all residue-field tests promoted to equality of the original Scheme morphisms.

Ten sources and105 declarations passed strict first-time checks plus endpoint-presence/recursive audit. The audit also checks actual specializations A=0,B=1 and A=1,B=0, so exceptional j-values are not silently omitted. Independent review and hosted integration remain pending.

This extends the previous Base N-specific associativity scope to arbitrary nonsingular rational coefficients. It does not claim new general-ring associativity, a Jacobian/Picard construction, polarization, PEL identification or final arithmetic. Existing general unit/inverse/commutativity endpoints can now be combined with this exact rational associativity when transporting operations through an actual over-Q isomorphism.
