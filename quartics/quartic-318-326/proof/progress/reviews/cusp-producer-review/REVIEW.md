# Independent cusp/energy linkage review

Result: accepted at the declared source scope. Fresh isolated copies replayed with `debug.skipKernelTC=false`; exhaustive recursive audit passed all62 declarations in10modules (nine cusp modules plus RationalAbsoluteHeight). Only propext, Classical.choice and Quot.sound occur. The copied Lean source files match their originals byte for byte.

## Mathematical checks

1. Whole-fiber avoidance is the correct invariant requirement. The intrinsic Weierstrass support has at most g³−g points, hence at most that many image values. Choosing among g³+1 distinct rational values produces a fiber avoiding the support everywhere. Q-definition of the same cover and intrinsic divisor then preserves avoidance at every conjugate. The note does not silently replace this with unrelated covers having the same j-value.

2. The actual modular transformation formula excludes c≠0 identifications in the high-imaginary-part region. The remaining translations have precisely the cusp width m. Normality of the principal congruence subgroup preserves the level after choosing a fundamental-domain representative. The explicit assumption −I∈Γ addresses the ineffective sign. Adding the cusp gives a completed embedded chart, so a centered disc meeting the cusp does not omit area or introduce a differential pole.

3. The norm and derivative ledger is consistent. The sigma3≤n^4 and Euler-product majorants bound G=qj by128. Cauchy on radius1/200 and the segment mean-value bound yield the stated errors at tiny q. Differentiating1728q/G gives the exact G−qG' numerator. The chain derivative m q_c^(m−1) is retained, so no cusp-width factor disappears. The inverse-q estimate is in the correct direction.

4. The radius is a strict subdisc of the completed chart. With rho=(Rc−rc)/2 and center norm≤rc, every point of the closed centered disc has norm≤(Rc+rc)/2<Rc. The exponential chord inequality gives rho≥exp(−21)/m≥exp(−21)/N.

5. The energy convention matches the independently proved Wronskian theorem exactly. In a holomorphic coordinate z=x+iy, (i/2) dz∧d(conj z)=dx∧dy. Thus a globally unit-normalized differential has local ordinary area energy integral |f|²≤1 on an embedded disc. Restriction is monotone because the density is nonnegative; no genus, degree, factor2 or covering multiplicity occurs. The neighborhood of the compact closed disc gives actual integrability. This supplies precisely the assumptions of ActualWronskian318.local_wronskian_bound.

## Preserved boundary

This review does not claim a new Lean construction of the modular curve/compactification, global Weierstrass divisor, orthonormal differentials, or chart pullback energy measure. Nor does it claim that Mathlib's actual j-function has been formally identified with the retained analytic G producer. The packet correctly exposes the holomorphic G/constant/norm hypotheses and labels the global geometric identifications as classical source inputs. FiveContact49Height remains an explicit upstream theorem, not established merely by the checked finite/analytic lemmas.
