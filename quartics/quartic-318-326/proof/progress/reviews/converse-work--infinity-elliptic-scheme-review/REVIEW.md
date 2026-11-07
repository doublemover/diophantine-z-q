# Independent review: actual two-chart Weierstrass scheme

Accepted at the declared scope. Fresh independent copies of the four modules
were strictly rebuilt and recursively audited: 148 declarations, standard
axioms only. All four source hashes match the frozen producer exactly.

## Exact object and map checks

The finite equation is y²=x³+Ax+B and the Y=1 equation is
z=x³+Axz²+Bz³. The actual infinity Jacobian is
1−2Axz−3Bz². Its principal open is smooth without a discriminant premise;
the explicit algebra point x=z=0 has Jacobian value 1 and yields a genuine
closed section in that chart.

The overlap maps use actual localization inverses. On D(y), the infinity
coordinates are x/y,1/y; on D(z), the finite coordinates are x/z,1/z. The
polynomial identities use only commutative-ring operations and the localization
unit equations. The two inverse proofs use localization and quotient-ring
extensionality, so there is no cancellation by a nonunit or hidden field/domain
assumption. The R-algebra structure and contravariant Spec orientation of the
overlap are correct.

The two infinity opens D(z) and D(Jacobian) cover because their generators span
the unit ideal by the displayed exact identity. The first is identified with
the smooth finite overlap; the second is the actual Jacobian localization.
Thus the whole infinity ring is smooth under precisely the discriminant-unit
hypothesis, including over rings with zero divisors.

The gluing uses an actual Scheme pushout of two proved open immersions, not a
parallel surrogate scheme. Mathlib's open-immersion colimit supplies actual open
charts and joint point coverage. Both maps to Spec(R) agree by the overlap
algebra map's R-linearity. The pushout structure map restricts to those exact
chart maps, and smoothness follows by the actual Zariski-local-at-source API.
The global infinity map is an actual section. The literal family uses the
previously checked discriminant unit on the same OpenJ base.

## Boundary retained

No proof is claimed here of identification with the homogeneous projective
cubic, properness, separatedness, relative group law, multiplication or
primitive torsion. Closedness of the section in the infinity chart is not
silently promoted to global closedness. Those are genuine remaining geometric
steps, and the global refined realization is not concluded. No mathematical,
map-direction or scope mismatch was found.

Replay: `bash snapshot/run.sh`. The review rebuilds these four copied modules,
not every imported dependency; exact dependency receipts are bound separately.
