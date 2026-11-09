# The actual sum of five quotient differential pullbacks

This continuation uses the independently accepted seven-source basis packet
`../recovered-five-basis-20261109`, preserved at commit
`2d147d358d23bba634a7daf34fcdc7fc9d5a4d33`. It does not change that packet.

## Exact objects and theorem

For the original complete source C and the five original completed elliptic
quotients E_i, the genuine canonical map

    direct sum_i H0(E_i, Omega(E_i/Q)) -> H0(C, Omega(C/Q))

which sums the five whole-scheme differential pullbacks is a Q-linear
equivalence. The coefficients on every source and target are restriction of
scalars through their original structure maps to Spec Q. The index is
`Option (Fin 4)`: `some i` is complementary quotient i, and `none` is the
fifth quotient. There are exactly five summands, with no excluded index.

`ActualQuotientDifferentialLinear318` packages the existing actual pullback
maps as linear maps. Each original normalized target invariant generates its
entire target global differential space over Q, by the previously checked
`ActualTargetRationalInvariants318` theorem. Their pullbacks equal the accepted
source basis entries with scalar exactly one. The fifth actual normalization
is not replaced by the auxiliary fifth function-field form.

`ActualFivePullbackEquivalence318` sums these maps on the finite dependent
product. Its inverse is explicit: take the corresponding accepted source
basis coefficient and multiply the original target invariant. It also proves
existence and uniqueness of this decomposition for every global source
section.

`ActualFivePullbackDirectSum318` constructs `DirectSum.toModule` from the
actual five pullbacks, identifies it with the finite product sum, and proves
that this exact universal-property map is the underlying linear map of a
linear equivalence. On each `DirectSum.lof` component it is precisely the
original canonical differential pullback.

## Relation to the Jacobian program

This is a theorem about global differentials of the five actual completed
curve morphisms. It is the cotangent-side linear-algebra input one expects
for a future represented Jacobian **norm** map Jac(C) -> product E_i.
It does not construct that map, identify a Jacobian cotangent space with
curve global differentials, prove an isogeny criterion, or establish finite
kernel/surjectivity of an abelian-variety morphism.

The separately constructed Picard presheaf pullbacks run in the other
direction, Pic(E_i) -> Pic(C). No tangent H1(O) or Serre-duality identification
is silently equated with this differential pullback. Those bridges, fppf
representability, group/Jacobian structures and any PEL conclusions remain
separate. No metric, height or all-integer witness theorem is claimed here.

## Verification and preservation

Final producer validation: all three sources pass a fresh strict replay,
and all 53 declarations pass the private-inclusive recursive axiom audit
with only propext, Classical.choice and Quot.sound. The seven accepted basis
sources and all 35 imported artifact hashes were verified before compilation.
The repository audit-history self-tests pass; that check is structural.

The receipt records the exact checked bytes. `check.sh` uses Lean
4.35.0 with `-j1 -M6144 -Ddebug.skipKernelTC=false` and checks all three new
sources before the private-inclusive recursive axiom audit. It requires the
source/dependency-verified checkpoint and exact accepted basis objects on
`LEAN_PATH`; it does not download or silently substitute dependencies.

The source policy is checked on a temporary ten-source composite consisting
of the unchanged seven accepted sources plus these three sources. That is a
source/import policy check only, not a promotion of the seven-source packet
into the baseline manifest or an independent compiler replay of it.

`APPLICATION.json` binds all nine application obligations. Independent
source-level review and branch/hosted admission are separate from producer
strict checks and must have their own records. The packet does not create a
PR or change the global progress manifest.
