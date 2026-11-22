# Exact chosen prime-field chart and generic-point transport

At one selected Gaussian factor, use the already accepted
residueEquiv s hs : ResidueField (BasePlace s hs) ≃+* ZMod p.
Use its coefficient map in the existing original Curve/Chart, then
the injectivity of the stock chart coefficient map and fraction ring
to lift it to the same two function fields. No new choice of a place,
a generator, a point, a rational function, or an automorphism appears.

The smallest native canary is
ActualGaussianWeberSelectedPrimeFieldChart318.selected_i_and_generic_coordinates.
It proves the signed integral i maps to the exact s, and separately
that X and Y map to the literal target xGeneric and yGeneric. It does
not call any Gaussian scalar theorem or any of the derivative/phase
gates. The second native receiver, exact
ActualGaussianWeberSelectedPrimeFieldFrobTransport318.primefield_frobenius_of_base_powers,
uses the strict stock additive coordinate map and coordinate_gaussian
to carry the *same* source point and positive powers to the actual
generic point over ZMod p, and expresses its target as the stock
coordinateHom of Frobenius. Its input hGen is tied to those same u,v;
it does not assert that the powers have been produced.

The final-interface-only draft is separate from both selectors. It
creates just one original selected witness, by the strict Descriptor62
actual_selected_descriptor, which supplies same four objects:
R=RatFunc.mk of the actual reduced primitive A,B and its hRat;
the residual affine point (u,v), its nonsingularity and hGen; and the
two degree bounds. Pass *that exact* R,u,v,hGen,hRat to:

1. ActualGaussianWeberSelectedSameRatioDerivative318
   .actual_selected_cross_of_descriptor; r2: 35/38 +629 only,
   OriginJet sole error, r3 scoped hF fix source-only here.
2. ActualGaussianWeberActualOriginPurePowers318
   .actual_scalar_pure_power_shapes; r1: 32/33 +544 only,
   terminal diagnostic repair r2 awaiting its separate exact result.
   This invokes the strict literal origin pole, not a second choice.
3. ActualGaussianWeberPrimaryOneAffineProbe318
   .positive_powers_from_same_named_probe; freeze exact 31/0 source-only,
   separate 28 strict donors plus 3 new; no global Frobenius result yet.
   It uses the actual selected residue equivalence to derive j^p=j
   and the explicit primary integer relation; never assumes every
   residue in an unrelated extension is fixed.

Then invoke the second canary with that same (u,v,hGen,hu,hv). This
realizes the general-coordinate generic ABI down the existing norm lane.
It is not the arithmetic Galois Frobenius, a claim about all geometric
points, or a completed producer of same-place residue norm. The old
unitFrobenius Tag.id is a one-term identity specialization at this
exact prime-field point; primitive torsion and actual arithmetic over-
place transport remain separate.

Repository payload is text only. Original official artifacts are SHA-
bound off-repository, not embedded. No local Lean, remote action or CI.
