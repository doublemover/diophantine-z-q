# Actual vertical relative-derivation bound

## Checked result

`VerticalDerivation318.lean` proves nine public theorems about a genuine
`Derivation R K K`, where `K` is the actual fraction field of a discrete
valuation ring `B`. If the derivation preserves `B` and kills a uniformizer,
then, for every fraction `x`, its derivative is `b*x` for some `b` in `B`.
The proof obtains the unit times integer-power decomposition from Mathlib's
actual DVR theorem; negative powers and the zero case are included.

Consequently the logarithmic derivative is integral, the canonical
multiplicative DVR valuation satisfies `v(D x) <= v(x)`, and the canonical
additive convention satisfies `ord(x) <= ord(D x)`. The rational-prime
uniformizer specialization derives `D(p)=0` from the derivation laws.
There is no assumed derivative valuation inequality or supplied fraction
unit/power decomposition.

## Exact remaining geometric input

The actual fraction-field derivation is provided, together with its
preservation of the integral local ring. In the intended application these
come from the relative differential in a local integral differential frame.
The reduced smooth vertical component supplies the fact that the rational
prime is a uniformizer. This packet does not construct a global regular model,
a differential frame, or an extension of an arbitrary integral derivation to
the fraction field. It does not yet assemble the bicanonical section's `J^2`
vertical integrality. Those are separate, visible interfaces.

## Verification

Run `bash verify.sh`. Lean 4.35.0 uses the project's pinned Mathlib revision
56a005855ea17e0b0958f73ec801ae140b0a1679. Every module is checked with
`debug.skipKernelTC=false`. The recursive audit covers all ten declarations in
the one mathematical module, permitting only `propext`, `Classical.choice`,
and `Quot.sound`. `PreservesIntegral` is the one definition; the other nine
public declarations are theorems. No repository files were modified.
