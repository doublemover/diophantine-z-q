# Actual vertical integrality of the two source sections

## Result

`literal_sections_integral` proves that both

- 2765952000² (D t)² / [t(t−32)(t−76832)(t+343)], and
- t times that expression

are in the image of the actual discrete valuation ring `B` in its fraction
field `K`. Here `D` is a genuine relative derivation preserving `B`, and a
rational prime `p` is a uniformizer of `B`. These are the local coefficients
of the source's `J²q0` and `J²q1` in an integral differential frame.

The proof does not assume a derivative valuation estimate, a maximum contact
order, a delta estimate, or the conclusion of local section integrality.
The preceding vertical-derivation packet obtains the derivative estimate from
the actual DVR fraction decomposition, including poles. This packet proves
integer divisibility of `J` by all six actual contact differences, derives the
nonarchimedean pairwise separation, and proves a four-factor multiplicative
inequality in the actual valuation's ordered value group. The case where `t`
is not integral is treated separately for the second section using exact
ultrametric equality. No residue-characteristic restriction is introduced.

The literal denominator and constant are exposed by a final wrapper. The
statement includes total field division even when a denominator vanishes;
in the geometric application `t` is a nonconstant rational function, so the
rational-function denominator is nonzero. No assertion that a pole is a valid
affine coordinate is inferred from total division.

## Scope still requiring geometric realization

A reduced smooth vertical generic point, its DVR/fraction field, and an
integral differential frame must be identified with the actual model and
its relative differential. The genuine `D` and its integral preservation are
inputs, not guessed local functions. The identification of these coefficients
with the global bicanonical sections, and extension from codimension-one
points on a regular model/stack, remain geometric inputs. The packet proves
the needed local integral coefficients, not a complete global model.

## Reproduction

Run `bash verify.sh`. Lean 4.35.0 with pinned Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679 checks the source with
`debug.skipKernelTC=false`. The independent recursive audit covers all 25
module declarations, including generated definitions; there are 12 public
theorems. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed.
The frozen dependency is `../vertical-derivation`. No repository/Git files
were changed.
