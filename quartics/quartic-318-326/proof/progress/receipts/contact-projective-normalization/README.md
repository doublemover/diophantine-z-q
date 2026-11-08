# Construct the global contact normalization

ContactProjectiveModel318 passes kernel replay and a recursive audit of all 25 declarations, using only propext, Classical.choice and Quot.sound.

The actual unbranched four-root contact cover is mapped into the existing projective-line scheme over Q. Its base coordinate is the contact coordinate t, not the modular j-coordinate. The same scheme map is identified in the reciprocal standard chart. The cover map is finite type, locally quasi-finite, separated, and quasi-compact.

Mathlib's actual relative normalization constructs a globally glued scheme over this projective contact line. The original cover embeds densely and openly into it, the map to the projective line is integral, and the global scheme is integral. No abstract global curve, gluing datum, or compactification map is supplied as a hypothesis.

This is not yet a proper/smooth projective model theorem. Finiteness of the normalization map, actual identification of the finite-contact and infinity neighborhoods with its open charts, normality/smoothness, and the PEL comparison remain to be proved. The word normalization names the actual relative-normalization construction and does not substitute for those remaining results.

Replay from the workspace root:

    flock compile-coordination/heavy.lock bash contact-projective-normalization/run.sh

See receipt.json and SHA256SUMS for the checked scope and hashes. No manuscript, shared branch, or PR edits were made. Independent review is pending.
