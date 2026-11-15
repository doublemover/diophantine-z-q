# Actual finite quadratic dual modules at nonunit normalized twists

Inactive two-module source draft, no local Lean or kernel verification. No active lane changes.

`QuadraticFiniteDual318` constructs the genuine module Hom_R(Q,R) for Q=R[z]/(z²-b), via its actual native quadratic presentation. The coefficient functional lambda(a+bz)=b yields the pairing x,y↦lambda(xy). Its explicit inverse sends a functional phi to (phi(z),phi(1)); this proves a perfect R-linear equivalence with the ACTUAL dual module. Multiplication/precomposition equivariance is proved explicitly for all x,y,z. No field, unit2, root-unit or unit-radicand hypothesis occurs.

The native quadratic trace equals pairing with the exact element2z. This is an equality of native quadratic-trace expressions, not an unproved comparison with a separately defined algebra trace. The different factor2z is retained and never canceled. The perfect coefficient functional exists integrally even when the trace pairing is degenerate or its different is nonunit.

Both arguments are transported through the actual algebra equivalence with the monic AdjoinRoot quotient. `NormalizedQuadraticFiniteDual318` specializes the construction to EACH of the four actual normalized equations z_i²=d_i(T-a_i) over V[T], including nonunit d_i and residue characteristic2. The transported generator sends the actual quotient root to1. It is a functional on a finite algebra, not the cotangent element dz_i.

This is a concrete finite-flat dual-module ingredient for dualizing comparison, not yet a relative dualizing sheaf theorem. The source does not rename a free coefficient module dualizing. It proves a base-linear perfect pairing plus explicit multiplication equivariance; it does not yet bundle a chosen algebra-module structure on the dual as an algebra-linear equivalence. Tensoring all four perfect dualities, comparison of the resulting actual Hom_{V[T]}(A,V[T]) with a relative curve dualizing sheaf and its fundamental class, and comparison to the original maximal regular model remain open. No cotangent/dualizing integral-lattice equality follows here.

The source/function-field domain batch is independently preserved, but not needed to prove this arbitrary-base finite-dual construction. Combining the two requires further actual maps, conormal and determinant work. Original global sections, integral KS210, metrics and GeometricRealization remain open.

Exact custom closure and pinned native QuadraticAlgebra/Dual APIs are bound for independent review and future hosted checking. Static hashes/source reviews are not elaboration or axiom acceptance; no resources or admissions are changed.
