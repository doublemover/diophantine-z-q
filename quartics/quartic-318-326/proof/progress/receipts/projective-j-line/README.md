# Actual proper projective j-line and source map

Fresh strict replay passes 76 recursively audited declarations in five modules, with only standard Lean axioms.

The target is genuine Mathlib homogeneous Proj of Z[X0,X1] (and the construction works over any commutative coefficient ring). Its degree-zero coefficient identification and actual structure morphism are constructed, and properness follows from Mathlib's proved projective-spectrum properness theorem. The two standard opens are actually isomorphic to Spec R[t], are open immersions, cover the target, and commute with the same coefficient base.

The homogeneous-fraction evaluation and double-overlap identities give equality of actual Scheme maps for a unit coordinate and its inverse. This is specialized to the literal OpenJModel318.Base N, whose actual j-coordinate is a unit. `OpenJProjectiveMap318.baseOpen` is an actual open immersion into the proper j-line, and its inverse-coordinate factorization and base-Z map are proved.

For any actual finite open-j algebra B, `coverMap N B` is a genuine scheme map to this constructed target. Its local finite type, separatedness and quasi-compactness are derived. Its actual source-to-relative-normalization map is an open immersion by the proved Zariski main theorem.

## Precise remaining boundary

This packet does not yet derive finiteness of the global normalization for this concrete map. The earlier global-normalization theorem gives that result when the actual second-chart scalar/localization data are supplied; binding the reciprocal open algebra and actual section-ring identifications is separate work. Accordingly no properness of this source normalization is claimed here, despite the target itself being genuinely proper.

The particular modular primitive-torsion cover, source component/domain, regular/semistable model, and arithmetic/PEL interpretation remain separate. No unconditional GeometricRealization or FiveContact49Height follows.

The generic dehomogenization `ProjectiveChart318` is consumed unchanged from the frozen projective-weierstrass-scheme packet. The elementary degree-zero/properness/cover/evaluation constructions specialize that same team's checked construction to two variables and the polynomial affine coordinate, with exact new source files and dependencies bound in the receipt. No files in the frozen dependency were changed.
