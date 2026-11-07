# Actual field-valued affine Scheme points

`AffineSchemeSolutions318` defines actual base-preserving morphisms Spec(K)→Spec(R[x,y]/equation). Mathlib's genuine fully faithful Spec/algebra-map equivalence and the previously proved quotient universal property identify those morphisms with exact coordinate solutions. This part works for any commutative coefficient algebra.

`LiteralWeierstrassPoints318` specializes to the actual OpenJModel over its literal base. Its model is the actual WeierstrassCurve.map along the field specialization. The mapped source discriminant is a unit, so every equation solution is genuinely nonsingular; no additional nonsingularity or point-membership premise is introduced. `fieldPointEquiv` is a bijection between the actual base-preserving field-valued affine Scheme points and all finite nonsingular points of that model. Infinity is excluded exactly because this is the affine chart. `fieldPointEquiv_coordinates` verifies the same literal x/y coordinates, not merely an unspecified bijection.

Two modules, 21 exhaustively audited declarations. Replay uses strict kernel checking and only propext, Classical.choice and Quot.sound. No original/frozen source was modified.

Scope: this is an actual affine Scheme/Weierstrass point identification over every field algebra of the literal base. It is not a relative group law, projective completion theorem, torsion Scheme or an identification with a specified arithmetic modular family. The actual base-change Scheme isomorphism is imported from the separate frozen packet. The diagnostic Check.lean is not part of the accepted manifest.
