# Actual infinity-output addition Scheme charts

Eight strict-kernel-checked modules construct two genuine regular addition maps from principal opens in the actual affine fiber product of the literal short Weierstrass curve. They extend the existing finite-output chord and tangent/secant charts across inverse pairs and doubling at 2-torsion.

## Actual formulas and objects

In the genuine tensor coordinate algebra, let d=x2-x1 and e=y2-y1 for the chord chart, or d=y1+y2 and e=x1²+x1*x2+x2²+A for the complementary chart. Set U=e²-(x1+x2)d² and V=e(x1*d²-U)-y1*d³. The actual input equations imply V²=U³+A*U*d⁴+B*d⁶ over every commutative ring. On the actual principal open D(V), the infinity-chart coordinates are x=U*d/V and z=d³/V. The equation z-x³-A*x*z²-B*z³=0 is proved before constructing the genuine quotient-algebra and Scheme maps. Each domain is an actual open immersion into the actual finite-pair Scheme fiber product, and both input projections and preservation of the original base are proved.

## Exact compatibility and point law

The finite/infinity compatibility theorem uses the genuine common localization and actual Scheme pushout, not agreement only on field points. On D(d), each infinity-output map agrees with its corresponding previously constructed finite-output chord or tangent map over every coefficient algebra. Every actual field point of either infinity-output domain is bound through LiteralCompletedPoints318.fieldPointEquiv to the genuine Mathlib point group. If d=0, V being invertible forces the two inputs to be inverse, and the Scheme output is the actual closed infinity section. If d is nonzero, the actual finite-chart compatibility and previously proved finite point laws give the addition formula. Both branches, including 2-torsion doubling, are therefore covered without a supplied group-law equality.

## Exact boundary

This packet does not yet prove all cross-chart overlaps, the four-open cover, the gluing of a finite-pair addition morphism, infinity-input charts, global group axioms, or a relative torsion scheme. The original literal open base and completed curve are the existing checked constructions; no specified arithmetic modular-family identification is inferred. The generic coordinate and Scheme identities do not assume characteristic zero or a field; the literal field-point specialization consumes the already established ellipticity of the literal model.

## Replay

Run bash run.sh. Every compilation uses debug.skipKernelTC=false. Audit imports all eight modules and recursively checks every declaration for only propext, Classical.choice and Quot.sound. Receipt manifests include accepted sources, logs, scripts and upstream packet hashes. The exploratory text files chord-identity.txt and tangent-identity.txt are not inputs to the Lean proof and are excluded from the accepted manifest.
