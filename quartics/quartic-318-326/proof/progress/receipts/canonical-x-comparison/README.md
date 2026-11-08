# Canonical rank-four arithmetic/analytic comparison

This packet removes the sign choice from the preceding arithmetic/analytic coordinate comparison.

## Constructed results

- Define the x-coordinate scale directly from the actual source and target coefficient functions as (target a6/source a6)/(target a4/source a4). Every permissible short-model scaling u has square equal to this scale. It is therefore independent of the square-root choice, nonzero, and holomorphic on the actual admissible upper-half-plane locus.
- Prove the exact universal third-division quartic transformation under x ↦ s*x, A ↦ s²*A, B ↦ s³*B. The transformed polynomial is s⁴ times the original, yielding an explicit root equivalence for invertible s.
- Use the universal property of the actual quartic AdjoinRoot algebra to identify its field points with actual third-division roots, then specialize the actual localized integral j-family at genuine analytic j.
- Combine this canonical coordinate map with the geometric packet's proved identification of the full diamond fixed algebra and the actual rank-four x-algebra. The map is multiplication by the explicit holomorphic x-scale, not an arbitrary four-point bijection.
- Prove that the target analytic quartic roots are exactly x-coordinates of actual order-three points on the genuine Eisenstein curve. The kernel of the x-coordinate map is proved to be precisely equality or elliptic negation. Hence its quotient is the actual sign quotient, and the final theorem identifies the literal fixed algebra's complex points with actual analytic order-three points modulo sign.

The earlier eight-point arithmetic fiber is kept distinct from this four-point sign quotient. The localization level N remains independent of the torsion order, which is three in this packet.

## Remaining boundary

This gives a canonical complex-point comparison of the specified rank-four arithmetic algebra, with a holomorphic coordinate expression. It does not assert an algebraic scheme analytification theorem or identify a global arithmetic moduli curve with the Γ1(3) or ΓH upper-half-plane quotient. It does not construct general-N arithmetic level schemes, resolve the excluded j-values 0 and 1728, or establish a PEL identification. Those remain separate obligations.

## Verification

Run build-all.sh while holding the shared compile lock. The five modules replay sequentially under Lean 4.35.0 with debug.skipKernelTC=false. The import-all audit recursively checks every public, private and generated declaration, allowing only propext, Classical.choice and Quot.sound. This is an author replay against pinned predecessor/Mathlib caches, not independent review or full dependency-closure replay.
