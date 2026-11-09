# Degree-zero and representability boundary

This is a bounded source comparison against pinned Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` and the current quartic source tree.
It identifies usable statements and the exact inputs still needing construction.
It is not a claim that no historical argument or external theorem exists.

## Support actually found and used

- `AlgebraicGeometry/Sites/Fpqc.lean` constructs the fppf and fpqc topologies,
  proves their subcanonicity, and recognizes singleton flat/surjective/locally
  finitely presented covers.
- `CategoryTheory/Sites/Over.lean` constructs the actual over-base topology;
  `SubcanonicalOver.lean` proves its subcanonicity.
- `CategoryTheory/Sites/LeftExact.lean` supplies sheafification from concrete
  limits and filtered colimits. The present packet constructs the missing
  `CommGrpCat` cover-colimit instance from the existing explicit cocones.
- `Sites/LocallySurjective.lean` and `LocallyInjective.lean` give the canonical
  unit's genuine local representative/equality properties. These are now tied
  to the original line classes, not merely asserted for an abstract functor.

## Results that do not yet provide a Jacobian

- `RingTheory/PicardGroup.lean` constructs a commutative ring's Picard group of
  invertible modules, including its relative affine group. It does not provide
  the degree of a line on the actual proper source curve or represent its
  relative Picard functor.
- `AlgebraicGeometry/EllipticCurve/Jacobian/` concerns Jacobian coordinates for
  Weierstrass points. These coordinates do not construct the Jacobian variety
  of the genus-five source.
- `Algebra/Category/ModuleCat/Descent.lean` proves comonadicity of extension of
  scalars along faithfully flat ring maps. Its header explicitly leaves the
  effective-descent pseudofunctor connection as a TODO. The general
  `CategoryTheory/Sites/Descent/` infrastructure is not already an instantiation
  for these original line sheaves.
- `AlgebraicGeometry/Sites/Representability.lean` proves representability by
  gluing an actual jointly covering family of relatively representable open
  immersions from schemes into a Zariski sheaf. Applying it requires constructing
  that atlas and proving its relative representability and coverage. A record
  that assumes those inputs would not prove Picard representability. Its
  `Type u`-valued target also requires the relevant size comparison for the
  current `u+1`-valued line-class sheaf.

## Concrete next steps

1. Use the actual finite-extension point and original structure square to
   obtain a genuine section after an explicit fppf field cover. The parallel
   contact-point work supplies this section without assuming a Q-rational one.
2. Normalize an original line by tensoring with the inverse pullback of its
   restriction to that actual section. Prove the original relative quotient
   is the kernel of section restriction, with actual inverse maps. This removes
   the base-line ambiguity. That kernel is **not** the degree-zero subgroup.
3. Construct actual rigidifications and their morphism/descent comparisons.
   The relevant automorphism control requires the original structure-sheaf
   pushforward comparison on these source families, not a result for unrelated
   elliptic families.
4. Construct a genuine degree notion on the actual geometric fibers and its
   tensor and base-change laws, or an equivalent algebraic-equivalence route
   with all necessary comparisons. The searched source modules do not currently
   provide that bridge. In particular, the existing generic field degree 16
   and quotient degree 8 theorems are not degrees of arbitrary line bundles.
5. Supply representability for the resulting actual functor, its degree-zero
   component and the required smooth/proper structure. The source model's
   already proved smoothness, properness and geometric integrality remain the
   correct geometric inputs, but they do not substitute for this construction.

The actual five-dimensional differential basis and the sum of quotient
pullbacks are separate useful data. Identifying them with the cotangent map of
the represented Jacobian norm requires the representation, the norm functor,
and the tangent/cohomology duality comparison. The current Picard pullback
sheaf maps have the opposite direction and are not silently identified with it.
