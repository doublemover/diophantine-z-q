# Identify the complete infinity function field

Two Lean modules pass kernel replay and a recursive audit of 78 declarations, using only propext, Classical.choice and Quot.sound.

FourRootGeneration318 proves that the four actual tensor root elements generate the full four-root algebra over its original base field. InfinityFieldEquivalence318 applies that result to the range of the previously constructed infinity-field map. Its range is a subfield, contains u, the three ratios, t=c0/u^2, all four original roots, and every rational function in t. The map is therefore surjective without a surjectivity or field-identification hypothesis. Together with the prior injectivity proof it gives an actual RingEquiv from the degree-eight Q(u) presentation to the full original four-root field, with exact base-coordinate and root compatibility.

This closes the surjectivity boundary explicitly left open in resumed-infinity-contact. The prior packet is unchanged. This packet does not yet glue the finite and infinity orders as open subschemes, prove properness or smoothness of a global model, construct a PEL object, or establish the final Diophantine theorem.

Replay from the workspace root under the exclusive compile lock:

    flock compile-coordination/heavy.lock bash infinity-field-equivalence/run.sh

See receipt.json and SHA256SUMS for verification evidence and frozen dependency hashes. No manuscript, shared branch, or PR edits were made. Independent review is pending.
