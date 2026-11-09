# Effective descent of specified rigidifications

Status: draft source, awaiting hosted Lean elaboration, recursive axiom audit and independent acceptance. No local Lean compilation was run. No baseline promotion or arithmetic theorem completion is claimed.

This packet joins the original affine faithfully flat line-descent reconstruction to the existing actual rigidified-line and pointed-pullback objects. For an actual commuting square e' ≫ f = g ≫ e with f and g affine, flat and surjective, it descends a specified local trivialization along e', provided that trivialization respects the original categorical g-double equation. The actual f-descent object and all its original double/triple laws are retained.

The original reconstructed line is unchanged. Its section trivialization is obtained by descending an actual compatible covering isomorphism. The same original f-covering comparison becomes a rigidification-compatible isomorphism without scalar correction. Compatible original local isomorphisms descend uniquely and retain their exact f-covering square. Finally, the original relative line-class pullback recovers the input local class.

New sources, in order:

1. RigidifiedOriginalDescentData318: original pointed descent data; explicit base-cover compatibility; the original reconstructed comparison transports the supplied trivialization.
2. RigidifiedEffectiveDescent318: actual trivialization descent, literal covering recovery, unchanged pointed comparison and uniqueness.
3. RigidifiedFaithfulDetection318: compatibility with specified rigidifications is faithfully detected on the base cover, without requiring the total-space map itself to be a cover.
4. RigidifiedIsoEffectivity318: original compatible isomorphism descent and exact uniqueness.
5. RigidifiedRelativeEffectivity318: consumer in the unchanged relative quotient, before sheafification.

Prerequisites are exact copies of affine-base-fppf-descent-r3 and rigidified-canonical-composition-r6, with their common producer checked byte-for-byte. The former remains hosted-pending; the latter has a successful scoped hosted result but is not promoted into the baseline. The copied root repair is inherited, not a new mathematical assumption.

Boundary: this does not yet identify every associated fppf sheaf value with rigidified classes, construct a degree-zero Picard scheme/Jacobian, prove representability, construct a principal polarization or identify a PEL abelian variety. The original trivialization's double compatibility is explicit input, not inferred merely from an equality of unrigidified classes. General fppf pointed covers require the subsequent refinement/assembly interface. No cartesian-square hypothesis is silently assumed.
