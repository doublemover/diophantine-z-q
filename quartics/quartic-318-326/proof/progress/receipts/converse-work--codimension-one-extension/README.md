# Actual codimension-one extension for UFDs

The seven public theorems in `CodimensionOneExtension318.lean` prove a genuine
localization-intersection statement. The local rings are Mathlib's actual
prime localizations embedded in the actual fraction field, not a predicate
that assumes an intersection identity.

For a fraction regular at a prime localization, an actual localized numerator
and denominator are obtained from that subalgebra's definition. Clearing the
denominator and using actual UFD reducedness shows the reduced global
denominator divides a denominator outside that prime, so it is outside the
prime. A nonunit reduced denominator has an actual irreducible divisor, giving
a contradictory prime localization. Thus the fraction belongs to the ring.
The Noetherian wrapper uses the actual ideal height and the principal ideal
height theorem to test only height-one primes. Coordinatewise extension in a
free frame is proved, including uniqueness in the fraction field.

This is the UFD specialization, not a formalized general Noetherian normal
domain intersection theorem. The intended application still must identify
actual regular local rings as UFDs, identify each height-one localization and
its section coefficients, and provide the actual line-bundle/sheaf/stack
realization. Global gluing is not silently inferred from the coordinate
statement. No scalar valuation or derivative estimate is repeated here.

Reproduce with `bash verify.sh`, using Lean4.35.0 and pinned Mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679. All sources use strict kernel checking.
The recursive audit covers all16 declarations (including generated/private
helpers), of which seven are public theorems. Only the three standard roots
propext, Classical.choice and Quot.sound occur. The official missing principal
ideal height dependency was obtained from the project dependency cache.
No repository or Git state was modified.
