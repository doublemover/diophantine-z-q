# Actual finite-branch charts of the twisted contact cover

This packet continues the actual four-root Q[t]-order at each of the finite contacts 0, 32, 76832 and -343. All four nonzero rational twists remain arbitrary. It supplies genuine algebra isomorphisms and a neighborhood containing the branch point, not a local-coordinate assumption detached from the original order.

## Checked results

- `LinearRootCoordinate318` repairs the unfinished quotient-coordinate construction. For every commutative ring and unit c, the actual quotient R[t,z]/(z²-c(t-a)) is explicitly isomorphic as an R-algebra to R[z]. The base coordinate maps to c⁻¹z²+a. Every other factor d(t-b) maps to (d/c)z²+d(a-b). Evaluation at z=0 is an actual algebra homomorphism. Over a domain, the transformed contact polynomial has root multiplicity exactly two.
- `ThreeRootOrder318` proves finite freeness, rank eight, faithful flatness, an etale criterion from actual parameter units, exact base change of the three polynomial quotients, and an actual regrouping of the original four-root tensor order.
- `FiniteBranchChart318` localizes the genuine ramified root line at the product of the other three factors. Distinctness proves that product is nonzero at z=0, and the branch evaluation extends to the localization. The localized original order is explicitly isomorphic to the residual three-root algebra. In characteristic different from two, it is finite free and etale of rank eight over this root-line neighborhood. The exact equation t-a=c⁻¹z² persists there.
- `FourRootPivot318` uses actual tensor commutation/association equivalences to move any of the four chosen roots to the first factor.
- `SourceFiniteBranch318` specializes every construction to each of the four literal rational contacts. Its finite/free/etale/rank-eight/faithfully-flat theorem has no supplied distinctness, unit, nonemptiness, rank, or etale hypotheses. The entire chart algebra is a domain, proved through its localization of the actual original domain order; no component is selected or assumed.

## Source and exact boundary

The coordinate t=32s is the Shimura contact coordinate, not the modular j-coordinate. The underlying mathematical branch inputs are already in the adopted Version 10 manuscript, paragraphs “Recovering the contact line from published quotients” and “Integral geometry and the degree 576 field,” followed by the metric-comparison paragraph (lines 6861–7025 in the pinned source). This is additional formal realization of those inputs for the constructed twisted cover, not a claim of a newly discovered manuscript gap. The manuscript is unchanged.

The packet does not identify the arbitrary-twist field with the actual PEL/Shimura source field, determine the source twists, construct the infinity chart or projective completion, provide the separate formal DVR ramification-index theorem, or establish controlled integral reduction and the final unconditional Diophantine theorem. In particular, arbitrary rational twists do not give the claimed fixed support of bad primes.

## Replay and audit

Run `bash run.sh > verification.log 2>&1`. The five modules and audit are rebuilt with `debug.skipKernelTC=false` against the existing pinned Lean 4.35.0/Mathlib installation. Every declaration in the five modules is recursively audited; only `propext`, `Classical.choice`, and `Quot.sound` are permitted. No placeholder, native-decision oracle, external field-isomorphism assumption, or imported axiom is added. `receipt.json` binds the source, runner, complete replay output, and the directly consumed frozen predecessor proof objects.

All changes are isolated to this packet. No repository/manuscript edits or PR were made. Author verification is not an independent mathematical review.
