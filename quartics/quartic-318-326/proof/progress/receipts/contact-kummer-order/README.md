# Actual twisted contact order and finite-etale cover

This packet constructs the actual Q[t]-order obtained by adjoining four square roots of c_i(t-a_i), with the exact finite contact coordinates a_i = 0,32,76832,-343 and arbitrary nonzero rational twists c_i. It is finite free of rank16 and is a domain. Its genuine rational-function base change is the preceding constructed degree16 Kummer field, via an explicit algebra equivalence and an injective original-order map.

## Proved objects and maps

- `FourRootOrder318` provides the actual four-quotient tensor algebra over any commutative ring, finite freeness/rank16, faithful flatness, an etale criterion from actual units, and the exact four-factor tensor base-change equivalence.
- `ContactKummerOrder318` instantiates the literal rational polynomial parameters. The actual order embeds into its genuine generic field. Localizing the base at precisely the four-contact product yields the actual rank16 finite-free, faithfully-flat etale algebra; its relation to the original order is an actual base-change isomorphism.
- `ContactKummerCover318` constructs the genuine Spec morphism over the actual open subset of the affine contact line, proves it finite, etale, flat and surjective, and proves the exact omitted rational-point criterion. No cover-existence or nonemptiness input is supplied.
- `ContactKummerOpenDomain318` proves the entire open-cover algebra is a domain, via actual tensor/localization compatibility and the original order domain. No generic component is selected or assumed.

## Remaining source boundary

The contact coordinate t is distinct from modular j. This is a concrete twisted contact cover over Q, not an identification with the source PEL/Shimura curve. Actual source twists, PEL function-field/model identification, finite-contact/infinity ramification and global integral good-reduction/Arakelov realization remain outside this packet. Arbitrary rational twists do not by themselves give a bound on bad rational primes. The final unconditional Diophantine characterization and full completeness remain open.

## Replay

`bash run.sh > verification.log 2>&1` freshly rebuilds all four modules with `debug.skipKernelTC=false` and then audits every declaration recursively. Only propext, Classical.choice and Quot.sound are permitted. Frozen predecessor field and polynomial/base-change proofs are used; no native evaluation or placeholders occur.
