# Actual cubic character quotient fields

This packet constructs the complementary cubic character fields inside the previously proved entire degree-sixteen contact field. It tracks the actual products of root generators, their radicands and their action under the actual root-sign automorphisms.

The endpoints identify each character field with its actual Galois fixed field, prove degree two over Q(t), relative degree eight and stabilizer cardinality eight, and specialize to the exact three remaining contact factors for each omitted branch. The omitted inertia flip fixes that field and the other three finite inertia flips negate its character root.

For the fixed arithmetic twists, a separate module turns the exact coefficient identities into admissible rational changes of variables between the four short Weierstrass models and the literal published models. This is stronger than equality of j-invariants. It is not a formal PEL source identification, a formal genus/Jacobian theorem for the degree-eight inertia quotients, or a formal quotient-by-full-two-torsion comparison. Those geometric inputs remain separate.

All module builds must hold the shared heavy.lock and use debug.skipKernelTC=false with a 180-second wall-clock cap per exploratory invocation. The recursive axiom audit checks every declaration from all four modules, permitting only propext, Classical.choice and Quot.sound.
