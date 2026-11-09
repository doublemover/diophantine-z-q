# Hosted revision after f38f064

This revision is pending hosted checking. The prior packet and its exact failure
logs are preserved unchanged. No local Lean compiler was run.

All 23 cohomology predecessors passed the hosted strict check. The new generic
split module failed because proof-only section hypotheses were omitted from the
theorem context. This revision explicitly includes `h`, and likewise includes
`hsplit`/`hcross` in the finite-family helper before those downstream proofs are
reached. No theorem statement, original map, normalization or geometric hypothesis
is weakened. The later generic/actual consumer and recursive audit remain pending.

# Actual source H1 and the common transfer kernel

This is an uncompiled continuation, not an accepted proof packet. No Lean build,
compiler or local axiom audit was run for these new sources. Hosted CI must check
all 26 modules and their recursive axiom audit before any verification claim.
Twenty-three predecessors are exact copies of `affine-open-comparison-20261109`;
`COPY_BINDINGS.json` binds the original sources, application and receipt. No
rational-H1 draft, differential-space replacement or new axiom is used.

## New mathematical content and its precise boundary

- `SplitAdditiveRetraction318`: a split additive pullback/transfer pair explicitly
  decomposes the whole source as the target times the transfer kernel. Coordinates
  are the original transfer and `x - pullback (transfer x)`; the inverse is the
  original pullback plus the kernel inclusion.
- `FiniteSplitTransfer318`: if all off-diagonal transfer/pullback composites vanish,
  the source decomposes as the product of targets times the **common** transfer
  kernel. Hence the sum of pullbacks is injective. Its surjectivity is equivalent
  to the common kernel being zero. Only with that additional hypothesis is it an
  additive equivalence, whose inverse is the actual tuple of transfers.
- `ActualFiveHOneDecomposition318`: applies the unconditional single-quotient
  decomposition to all five original completed quotient maps, including the fifth
  target. Its carrier is the unchanged `SourceHOne`, actual cohomology of the
  original contact curve. The trace normalization remains the original trace/8.
  It states the two open simultaneous hypotheses as `CrossTermsVanish` and
  `JointlyDetectZero`; neither is assumed globally or silently discharged.

The indexing set is exactly `Option (Fin 4)`: `none` denotes the fifth quotient,
and `some i` the four complementary quotients. Every formula quantifies over the
entire set and uses all five original additive maps in their original direction.
Each coordinate decomposition is unconditional apart from the already proved
individual splitting. The fivefold decomposition and equivalence are explicitly
conditional. No fivefold H1 spanning, H1 dimension, Picard tangent comparison,
Serre duality or Jacobian isogeny is established by this packet.

## Dependency interpretation

The accepted differential-basis / differential-pullback equivalence has a
*different carrier*. It cannot discharge `JointlyDetectZero` without another
proved comparison and compatibility theorem. Similarly, five individual split
injections alone do not discharge `CrossTermsVanish`: two different targets can
have overlapping images. Even cross-term vanishing does not force the common
kernel to vanish; a source can have an extra summand invisible to all transfers.
The new decomposition identifies that possible summand explicitly rather than
removing it by a dimension assumption.

A next geometric route must prove off-diagonal identities for these exact maps
(for example, using actual sign actions and transfer equivariance) and eliminate
the common kernel (for example, by a genuine whole-H1 calculation or an applicable
perfect pairing). Such constructions remain open, as does rational linearity in
the separate rational-H1 continuation. Nothing here changes their status.

## Validation and integration

`intake.json` registers the complete dependency closure for the repository's
existing hosted experiment checker. Shared `packets.json` activation is owned by
the integration coordinator. Structural checks are not Lean verification.
No earlier receipt, review, frozen source or accepted progress manifest is edited.
No independent acceptance has been authored for these changes.
