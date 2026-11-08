# Bind infinity charts to the original fraction field

Three modules pass kernel replay and a recursive audit of all 107 declarations, using only propext, Classical.choice and Quot.sound.

- TensorFractionField318 proves that an actual generic tensor algebra identified with a field is the fraction field of the entire torsion-free domain order, under the specified embedding.
- InfinityFractionField318 applies this to the actual infinity Q[u]-order and transports the result through the proved infinity-field equivalence. Its fraction field is the whole original four-root contact field.
- InfinityOpenFractionField318 constructs the actual localization map from that order to the rank-eight etale infinity neighborhood, proves it is localization at the coefficient product, extends the original-coordinate embedding, proves it injective, and identifies the neighborhood's fraction field with that same original field. Compatibility with every element of the unlocalized order is explicit.

These are actual IsFractionRing statements for the specified maps, not abstract equality of degrees. They close the missing chart fraction-field identification but do not yet identify finite and infinity schemes along their overlap or prove the global normalization finite, proper, normal, or smooth. The PEL and integral-reduction comparisons remain separate.

Replay from the workspace root under the exclusive compile lock:

    flock compile-coordination/heavy.lock bash contact-fraction-fields/run.sh

See receipt.json and SHA256SUMS for the verified scope and hashes. No manuscript, shared branch, or PR edits were made. Independent review is pending.
