# Actual whole-cubic x-coordinate morphism

For every commutative ring R and A,B:R, this packet constructs an actual morphism from WeierstrassGluing318.scheme A B to the genuine ProjectiveJLine318.scheme R. It has no discriminant, reducedness or domain hypothesis. Its finite-chart restriction is precisely polynomial evaluation at the original affine x-coordinate followed by the standard projective chart1.

On the original infinity chart I=R[x,z]/(z-x^3-A*x*z^2-B*z^3), put D=1-A*x*z-B*z^2. The exact identity z*D=x^3 and the expression D+z*(A*x+B*z)=1 prove that D(z) and D(D) cover the entire infinity chart. The latter has the regular reciprocal coordinate x^2/D. On the actual common localization I[D^-1][z^-1], this reciprocal times x/z is one. This identity holds in the whole algebra over arbitrary rings, without generic cancellation.

The actual common-localization square is proved cartesian using the exact principal-open ranges. Its coordinate maps agree in the actual projective line by its standard unit-coordinate transition. The full infinity map is glued on that actual cover; it then agrees with the finite x-map on the original completed-cubic overlap. The actual completed target pushout supplies xMap. Both chart restrictions, its exact R-structure square and separatedness are proved.

These four source files have successful bounded strict per-module checks with debug.skipKernelTC=false. The final x-structure check in check-41 succeeded before the subsequent unrelated source-consumer draft failed to locate an existing dependency; that raw log is retained rather than relabeled as a whole successful batch. Integrated replay and recursive audit are pending hosted CI; independent review is separate. No redundant whole-chain cloud replay was run.

This is the actual published Weierstrass x-coordinate, not yet the original contact t-coordinate. The nonzero affine scaling/translation, its source composite, character-map finiteness and relative-normalization comparison are separate consuming joins. No Jacobian, group quotient, polarization, maximal-order, PEL or Kodaira–Spencer assertion is made here.
