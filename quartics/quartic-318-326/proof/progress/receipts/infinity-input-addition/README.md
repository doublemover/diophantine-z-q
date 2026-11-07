# Actual infinity-times-finite addition chart

Seven modules construct a genuine regular Scheme morphism on an open neighborhood of the entire infinity-times-finite locus, prove its actual relative unit law, and prove exact ring-level compatibility with the ordinary chord morphism on the finite input overlap.

## Actual regular formula

For the actual infinity input (u,v) satisfying v-u³-Auv²-Bv³=0 and finite input (x,y) satisfying y²-x³-Ax-B=0, set k=1-Auv-Bv² and h=k-xu². The actual tensor coordinate algebra is InfinityChart318.Ring A B tensor ShortAffineJacobian318.Ring A B. The domain is its genuine principal localization D(h), not a formal completion. Write

Nx = xk²-2kyu+(x²+A)ku²+(Ax+2B)u⁴,
Ny = yk²-(3x²+A)k²u+3xyk²u²-(x³+3Ax+4B)ku³+2Ayku⁴+y(Ax+3B)u⁶.

The output is the actual finite-chart point (Nx/h²,Ny/h³). The kernel derives k²(1-k)=Au⁴k+Bu⁶ from the infinity equation and verifies Ny²=Nx³+A*Nx*h⁴+B*h⁶ from both actual input equations. Thus the output is a genuine quotient-algebra map and Scheme morphism. The domain is proved an open immersion into the actual infinity-chart/finite-chart fiber product, and the output preserves the original base.

## Unit law and exact overlap

Along the actual infinity section u=v=0, k=h=1 and Nx=x, Ny=y. The entire finite Scheme factors through D(h), its first product projection is the genuine infinity section, its second projection is the identity, and its output is the actual finite-chart inclusion. This is an equality of Scheme morphisms, not merely field-point evaluations.

Two generated polynomial certificates prove the denominator-cleared ordinary-chord compatibility. Their coefficients are checked by Lean ring arithmetic; Python/Sympy is not in the trusted proof path. Unit-only cancellation then proves the actual quotient maps and Scheme maps agree with the finite chord law over every common coefficient algebra satisfying the literal input coordinate transitions u=x1*v, y1*v=1, x=x2 and y=y2. These are input-chart transition identities, not a supplied addition equality. The overlap automatically has the ordinary chord denominator invertible, derived from (xv-u)u²=-vh. No field, reducedness, density or characteristic hypothesis is used in this compatibility theorem.

## Exact remaining boundary

This packet exports the arbitrary-coefficient-algebra overlap equality. A separate next join must realize its universal overlap/factorization in the global input cover and glue it to the completed finite-pair addition map. Integrated all-field-point evaluation of this new chart is not asserted here. The symmetric finite-times-infinity chart and both-infinity chart, the full global input cover, group axioms and relative torsion schemes remain separate. No arithmetic modular-family identification is inferred.

## Replay

Run bash run.sh. Every compilation uses debug.skipKernelTC=false. Audit imports all seven modules and recursively rejects every axiom except propext, Classical.choice and Quot.sound. generate_identity.py and generate_overlap.py reproduce the literal polynomial certificate sources; running them is optional for proof replay, which consumes the hash-bound Lean sources directly. No original/frozen upstream source or repository file was changed.
