# Concrete five-contact producer assembly

Strict-kernel PASS: one module, seven public theorems,87 exhaustively audited declarations. Most declarations are generated record projections, not additional geometric theorems. Only propext, Classical.choice and Quot.sound occur.

Final API: `FiveContactProducer318.five_contact_of_realization : GeometricRealization -> ContactHeight318.FiveContact49Height`.

`GeometricRealization` is explicitly unproved. It requires actual CM or non-CM producer data for each primitive noncontact rational input. Neither final contact height, final Jacobian height nor854R is a field of the data. The exact literal radical/support and projective-coordinate height are bound internally. The records retain actual geometric/model/period/Arakelov/image/isogeny/contact-metric identifications, whose source applications are tracked in PRODUCER-LEDGER.md.

This is not an unconditional proof of FiveContact49Height or literal source soundness. It does not introduce an axiom or silently accept the existence statement. The distinction between source-level classical proof validation and kernel construction of the actual geometry is part of the deliverable.

The packet also proves the actual rational contact-coordinate height equality, scaled metric coordinate equality, branch avoidance from the five literal forms, and support>=1. CM surface-to-contact normalization is corrected; the obsolete generic contact854R application is not consumed. Auxiliary averaging/model fields are kept separate from the controlled isogeny field degrees.

Replay: bash build.sh. Build/Audit use debug.skipKernelTC=false. The source dependencies were frozen before this receipt. No repository/Git changes were made.
