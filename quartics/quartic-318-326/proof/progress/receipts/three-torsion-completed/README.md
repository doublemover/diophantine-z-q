# Actual completed tripling kills the rank-eight torsion scheme

Status: four new modules strictly checked with debug.skipKernelTC=false; recursive import-all audit passed 27 declarations. Hosted integration and independent source review are pending. These were bounded first-time checks, not a full dependency rebuild.

CompletedTangentRestriction318 proves the original nonvertical tangent addition is the restriction of the actual completed addition. Its generic doubling restriction applies to every Scheme test object equipped with the actual tangent-diagonal lift, without a pointwise extension assumption.

ThreeTorsionCompletedDoubling318 defines the exact completed inclusion as the existing ThreeTorsionScheme318.inclusion followed by the original finiteChart. It proves this inclusion followed by actual CompletedIteratedAddition318.doubling equals the same inclusion followed by the actual global negation. The proof joins the existing entire-ring tangent equality and the exact input-chart restriction.

ThreeTorsionCompletedTripling318 compares the actual tripling-input pair with the actual anti-diagonal evaluated at negation. Its second projection uses negation_twice. The already checked global antiDiagonal_addition then proves inclusion_tripling: the entire rank-eight scheme followed by the actual tripling Scheme morphism equals its structure map followed by infinity.

ThreeTorsionTriplingFiber318 defines the genuine categorical pullback of that tripling map and the zero section. It constructs the canonical map from the rank-eight scheme into this actual fiber, verifies both projections, and proves uniqueness for those projections.

Hypotheses: an arbitrary commutative coefficient ring, invertible 3, and unit short-Weierstrass discriminant. Nilpotents are retained. The argument uses no field-point shortcut, commutativity, associativity, or supplied global group structure. The underlying tripling composite is exactly P ↦ (P+P)+P. No equality with the full tripling fiber, complement of its zero section, or global multiplication-kernel isomorphism is asserted. No PEL or final arithmetic witness claim is made.
