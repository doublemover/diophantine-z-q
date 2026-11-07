# Actual formal stabilizers in the five-contact quotient

Strict-kernel PASS: one module, five public theorems,28 recursively audited declarations (including structure projections). Standard axioms only.

`Action` is an actual faithful zero-constant formal power-series action: its multiplication law is stated using Mathlib substitution, and its identity is X. The linear coefficient is proved to be a monoid character. For an exponent-two group over a field of characteristic different from2, the actual substitution square is identity. The checked tame-coordinate averaging/compositional-inverse theorem then proves that tangent1 forces the group element to be1. Thus the tangent character is injective, without assuming tangent faithfulness. Every tangent value squares to1 and lies in{1,-1}; the actual finite group consequently has cardinality<=2.

This is the exact formal-local stabilizer fact used for the Atkin–Lehner W=(Z/2)^4 five-contact branch argument. Applied to the actual stabilizer's completed local action, it excludes larger stabilizers and collisions of different involution fixed loci in residue characteristic different from2. If the geometric pullback action uses the opposite composition convention, use the opposite group; cardinality and exponent-two condition are unchanged.

The actual smooth-curve point/completed-local-ring identification, faithfulness of the curve action on a local neighborhood, and passage from a special fixed point to a mixed-characteristic relative chart remain geometric facts. This packet does not treat substitution with a nonzero constant in the maximal ideal, nor claim the tame special-point lifting theorem from a zero-constant field calculation. Those boundaries remain explicit in FIBER-PRODUCER.md.

Dependency: frozen tame-formal-coordinate-bridge/TameCoordinate318.lean, which proves actual averaged parameter invariance and uses the actual compositional inverse. No cyclicity or torsion-free tangent hypothesis is supplied. Replay with bash build.sh.
