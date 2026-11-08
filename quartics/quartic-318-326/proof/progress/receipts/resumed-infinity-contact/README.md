# Infinity coordinate and its degree-eight contact algebra

This isolated packet continues the actual twisted four-root field with arbitrary nonzero rational twists c. It does not assume those twists match the PEL curve.

## Mathematical content

- In the original four-root field, define u=c₀/y₀ and rⱼ=yⱼ₊₁/y₀. The exact equations are t⁻¹=c₀⁻¹u² and rⱼ²=(cⱼ₊₁/c₀)(1−aⱼ₊₁u²/c₀). All denominators are proved nonzero. The source t and all four original roots are explicitly recovered from these coordinates. The infinity coordinate u is transcendental, so Q(u) genuinely embeds into the original field.
- The three quadratic polynomials in u have independent squareclasses, proved by squarefreeness and pairwise coprimality even when individual quadratics split over Q. Their actual tensor algebra over Q(u) is a field of degree eight.
- The Q[u]-order is a domain via its explicit generic-fiber isomorphism with that field. Inverting the product of its three coefficients gives a finite-free, faithfully-flat, etale, rank-eight domain algebra. Evaluation at u=0 extends to its base localization, so the infinity point is not removed.
- The degree-eight field maps injectively into the original contact field, sending the base variable to u and its three roots to the ratios rⱼ. This is an actual map, with the new Q(u)-algebra structure specified explicitly.

## Exact boundary

The packet supplies an actual infinity neighborhood algebra and a field embedding with coordinate identities. It does not yet prove that this embedding is surjective, identify the chart's fraction field with the whole original field, glue the chart to the finite charts, or construct the global smooth/proper curve. It also does not construct a PEL object, prove an integral good-reduction theorem, or complete the unconditional Diophantine endpoint. The coordinate t is the Shimura contact coordinate t=32s, not the modular j-coordinate.

## Verification

The runner uses the pinned Lean 4.35.0 installation and debug.skipKernelTC=false. Audit.lean recursively checks every declaration in all six modules and rejects every axiom except propext, Classical.choice, and Quot.sound. See receipt.json for the completed verification status, hashes, and exact remaining scope. A compile pass verifies these statements, not the external PEL comparison or entire manuscript.

No manuscript, shared branch, or PR was edited.
