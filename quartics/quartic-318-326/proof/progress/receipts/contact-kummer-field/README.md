# Actual twisted four-contact Kummer field

This packet constructs an actual degree16 field and identifies it with the actual four-polynomial tensor algebra for the finite Shimura contact coordinates t=0,32,76832,-343. All four nonzero constant twists remain arbitrary. The coordinate t=32s is distinct from the modular j-coordinate.

## Proved results

1. `SquareReflection318.fraction_square_iff` proves that a square of an integral element in the actual fraction field of a normal domain descends to that domain, via a genuine monic integral equation. `quadratic_square_iff` proves the exact two-class square reflection in the actual quadratic algebra by its two coordinates.
2. `LinearContactSquareclass318` proves every nonempty product of distinct linear contact factors, multiplied by any nonzero constant, is not a square in the actual rational-function field. It uses actual squarefree polynomial products and fraction-field integral closure, not a detached valuation assumption. The four exact contact coordinates are independently proved distinct.
3. `QuadraticTower318` constructs four actual quadratic algebra field structures from the exact squareclass independence criterion, proves the successive square-reflection formulas, and computes degree16.
4. `SourceKummerField318` proves that criterion for arbitrary nonzero constant twists of the four exact source factors. Its final field and degree theorems have no supplied irreducibility, field-degree or squareclass premise.
5. `KummerTensorField318` constructs an actual algebra isomorphism from the tensor of the four polynomial quotients F[Z_i]/(Z_i^2-a_i) to that field. Thus the actual raw four-root algebra is a field of degree16, rather than merely having the same dimension as some field.

## Source and remaining boundary

The adopted Version10 proof, in its five-contact height argument around the paragraphs “Recovering the contact line from published quotients” and “Integral geometry and the degree576 field,” determines the contact coordinates and proves local tame equations w=z². It does **not** specify a global untwisted Kummer equation. Accordingly this packet retains arbitrary nonzero constant twists and does not identify any guessed twist with the actual PEL/Shimura curve. Source function-field/branch/model identification, integral global realization and the final unconditional theorem remain open. No modular j and Shimura contact coordinate are silently identified.

## Replay

`bash run.sh > build.log 2>&1` strictly kernel-checks the five modules and exhaustive declaration audit against the pinned Lean4.35.0/Mathlib. Allowed axiom roots: propext, Classical.choice, Quot.sound. Actual tensor presentations reuse the listed frozen sibling polynomial-quotient/base-change packet. No placeholders or native-decision oracle are used.
