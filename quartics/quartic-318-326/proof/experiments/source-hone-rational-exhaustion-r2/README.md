# Structural rational source H1 and original five-map exhaustion

This 55-source packet is uncompiled and awaiting hosted strict checking, recursive
axiom auditing and independent acceptance. No local Lean compiler was run. It
combines the concrete 47-source spanning calculation with three exact earlier
structural scalar sources and three exact already-hosted decomposition sources.
The scalar sources were read directly; their old profiling logs are not accepted
validation. All copies are pinned in COPY_BINDINGS.json.

ActualSourceHOneRationalSpanning318 equips the unchanged actual SourceHOne with
the structural rational action induced by multiplication on its original sheaf.
It does not infer a Q-space from the additive surjection. Original boundary and
difference become rational-linear by the unique rational scalar compatibility of
additive maps between Q-modules. Their kernel/range equality is the same original
chart-image statement, now a genuine equality of Q-subspaces. The canonical
linear kernel quotient identifies representatives with the original boundary.
The exact five-coefficient map becomes linear and remains surjective, yielding
finite-dimensionality and a genuine upper bound finrank_Q H1 <= 5.

ActualFiveHOneRationalExhaustion318 puts structural Q-actions on the five unchanged
target groups, and linearizes the original pullback, normalized transfer, sum of
pullbacks and tuple of transfers. Individual original splittings prove that all
five targets are finite-dimensional. Two geometric inputs remain explicit:

- CrossTermsVanish: each normalized transfer kills every other pullback image.
- TargetsNonzero: every original target H1 has an actual nonzero element.

Under these two inputs, the target product has rank at least five and injects
through the original sum of pullbacks into a source of rank at most five. Equality
of finite dimensions therefore gives surjectivity, source rank exactly five, and
zero common transfer kernel. The final rational equivalence has exactly the
original sum of pullbacks as forward map and all original normalized transfers as
inverse. Unlike the prior conditional endpoint, common-kernel exhaustion is now
derived from the concrete coordinate calculation, not a separate hypothesis.

Neither displayed geometric input is proved by this packet. It does not claim
unconditional rank five, coordinate-class independence, actual quotient-pullback
spanning or final isogeny. The next work must establish cross terms by genuine
sign-action compatibility and target nonvanishing, or construct the five original
coordinate residue functionals and compare the actual quotient classes directly.
No differential carrier, genus label or unrelated abstract H1 replaces the
original groups. Every scalar action, linearization and sum retains the original
maps and their normalization.

Pinned Mathlib rational-linearization, linear first-isomorphism, finite-dimensional
surjection/injection and finrank-product statements were read at
56a005855ea17e0b0958f73ec801ae140b0a1679. These API comparisons and the structural
checks are not kernel validation or independent mathematical acceptance.

## Revision r2

Run 42576170502 at 1ec2917 checked the first31 modules and the reverse section-
kernel branch, but the forward branch still used opaque S.X2/S.X3 in its
existential witnesses. The only changed Lean line now constructs those witnesses
with explicit U and V. The naturality proof already uses those exact concrete
opens; this aligns its target without changing any map, section or theorem.
Original tested45-source bytes and logs are preserved under
source-hone-small-poles-r1/hosted-failure-1ec2917. The55-source r1 is unchanged.
This revised closure still awaits hosted checking and independent acceptance.
