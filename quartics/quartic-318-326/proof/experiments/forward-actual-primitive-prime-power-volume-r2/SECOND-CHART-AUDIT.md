# Actual second-chart obstruction audit

Finding is at the original Gaussian-source consumer, not a counterexample to the existing abstract obstruction theorem.

Pinned repository manuscript `quartics/quartic-318-326/docs/sources/quartic_v10.tex` lines 16771–16800 explicitly uses `(P,D)` in chart x1=t but `(P',K)` in chart x0=t. It does NOT replace K by unshifted D in the second chart. Earlier `LiteralAdjacentNormSlice318.second_chart_iff` correctly reaches P',K. `OriginalNormPointSieveTail318.pointObstruction` instead defines both chart obstructions with unshifted D. Subsequent anisotropic residue, quadratic norm-factor eliminant, full-shear rectangle, all-prime and good-family theorems preserve precisely that defined predicate. They must not be advertised as the complete original second Gaussian chart.

Exact original counterexample: kappa=1, (a,b,c,d,w)=(-5,-1,-5,-1,0), x0=t=-10, x=b-d=0,z=b+d=-2,p=17. Original quadric equation is zero. Adjacent norms G=H=17; P'=0 and K=0 modulo17. The current D=(t²+x²)(t²+z²) is13 modulo17. All current exclusions p>3,p∤kappa,p∤t hold. This refutes the missing source implication.

Correct identities:
- K-D=P(P+2t²−2xz), so the FIRST chart source transport remains valid.
- (t+2)²K−t²Dshift = P' * [k(t+2)w²+2t³+8t²−2txz+8t−2xz], where Dshift=((t+2)²+x²)((t+2)²+z²).
- At t=-2, K=(k w²−xz)²+4(x+z)². On x=0 it is k²w⁴+4z², and on z=0 it is k²w⁴+4x². The shifted D collapses to x²z², so it cannot replace K at this exceptional label.

Correction requirements:
1. Preserve all currently proved/source-reviewed first-chart estimates and the independent original-lattice/index/Rankin work. They do not rely on a second-source identification.
2. Build the second actual pair P',K through its genuine quartic eliminants, or use shifted norm factors only at primes avoiding t+2 and separately handle primes dividing t+2 with the actual K. The label t and original modulus q(t) MUST remain unchanged; relabeling t+2 would alter lattice/index and choice order.
3. Handle actual t=-2 using K (not the old unshifted-D exceptional positive eliminants). The existing abstract D-exception proof is still its own statement, but is not the original Gaussian exception.
4. Recheck local residue counts, leading coefficients/shears, resultant nonzero arguments and integer zero cylinders at the actual corrected pair before claiming a global source count. There is no shortcut from a missing implication to an assumption supplied by the consumer.
5. One-chart-only coverage would additionally need the original exceptional branch p|x1 but p∤x0, plus R=0 and p|x0,x1. No such coverage has been supplied.

`check_second_chart.py` independently symbolically checks both polynomial identities, exceptional restrictions, and the concrete original counterexample. No Lean is run locally. This audit is not a proof certificate or a claim that the final Gaussian sieve is complete.
