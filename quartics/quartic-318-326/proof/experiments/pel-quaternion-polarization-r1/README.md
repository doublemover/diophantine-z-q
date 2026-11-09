# Concrete quaternion order and perfect trace pairing

Construct a concrete rational quaternion carrier with the exact μ²=−210 positive-involution convention, faithful real matrix action, and an explicit Rosati-stable integral order on which the same alternating trace form is perfect.

The specified lattice is the exact basis [1,i,(1+j)/2,i/2+k/10] in B=(-210,5). It is not the naive Z[1,i,j,k], and not a line bundle on the contact curve. The supplied source receipt classically invokes B210, a maximal order and an automatic polarization; this packet constructs concrete algebra and lattice prerequisites instead of assuming those objects have already been formalized.

The positive Rosati trace and the Riemann-form sign are different statements. Our E=Tr(μ^-1*x*bar(y)) is retained exactly. With the analytic upper-half-plane right complex structure, the positive form is -E in the E(x,Jx) convention. The analytic consumer owns that proof.

## Source-to-consumer obligations

1. **Concrete algebra, not a curve label.** Required: The PEL algebra must not be confused with the separate encoding elliptic coefficient or genus-five contact Jacobian. Constructed: B is literally Mathlib QuaternionAlgebra Q(-210,0,5), with μ=i, j²=5, ij=-ji and an explicit μ inverse. Its reduced discriminant210 and identification with the named source algebra still require local classification. Evidence: PELQuaternionAlgebra318.

2. **Exact positive involution.** Required: The source convention is μ^-1*bar(x)*μ, not arbitrary conjugation. Constructed: The involution is constructed with that formula, its coordinate signs, anti-multiplication and involutivity proved. Its positive trace is exactly2(r²+210i²+5j²+1050k²) and is strictly positive at every nonzero rational element. Evidence: PELQuaternionAlgebra318.rosati; positive_trace.

3. **Same alternating trace form.** Required: The action and polarization candidate must refer to the same carrier and orientation. Constructed: E(x,y)=Tr(μ^-1*x*bar(y)) is proved bilinear, alternating, nondegenerate, and E(a*x,y)=E(x,rosati(a)*y). No unrelated elliptic Weil pairing or dimension argument supplies this. Evidence: PELQuaternionAlternatingForm318.

4. **Faithful real splitting input.** Required: The analytic period carrier requires an actual algebra hom and the same adjoint. Constructed: The explicit rational quaternion ring hom into real2x2 matrices is proved multiplicative and injective. It sends μ to sqrt210 times the rotation and j to diag(sqrt5,-sqrt5); Rosati maps exactly to transpose. Evidence: PELQuaternionRealRepresentation318.representation; representation_injective; rosati_transpose.

5. **Actual integral order.** Required: A rational pairing alone does not construct a PEL lattice. Constructed: The basis1,i,(1+j)/2,i/2+k/10 gives a specified subring through an explicit integral multiplication polynomial. The carrier is exactly the range of the four-integer-coordinate embedding, with an additive equivalence. It contains μ and is stable under the same Rosati involution. Evidence: PELPrincipalOrderCoordinates318.order; coordinatesEquiv; mu_mem; rosati_mem.

6. **Perfect integral pairing.** Required: Principal-lattice compatibility must be proved, not inferred from rank or integrality. Constructed: The same unrescaled trace form has exact integer Gram[[0,-2,0,-1],[2,0,1,0],[0,-1,0,0],[1,0,0,0]]. Every integral linear functional has an explicitly constructed unique representing coordinate vector. The naive order is separately shown not perfect, preventing substitution of the wrong lattice. Evidence: PELPrincipalOrderPerfect318.perfect; PELQuaternionIntegralOrder318.standard_pairing_not_perfect.

7. **Period positivity convention.** Required: A positive Rosati trace is not yet positivity of a Riemann form for the chosen complex structure. Constructed: This packet retains E and μ unchanged. For the standard upper-half-plane right complex structure, E(x,Jx) is negative; the analytic worker explicitly uses -E, equivalently E(Jx,x). Exact period compatibility and positivity are separate consuming proofs, not hidden sign changes here. Evidence: README.md; PELQuaternionAlternatingForm318.pairing.

8. **Remaining PEL/Jacobian identification.** Required: The abelian surface, maximal order, moduli and original contact source must be constructed or compared. Constructed: Reduced-discriminant/maximality classification, compact complex torus and algebraization, represented abelian scheme with order action, determinant condition, principal polarization on that scheme, actual PEL moduli/contact identification and integral KS/Hodge theorem remain separate. Perfect lattice does not establish all those conclusions. Evidence: README.md; source MAXIMAL-KS-PRODUCER section1.

9. **Historical application and validation.** Required: Classical producer hypotheses and formal implementation must remain distinct. Constructed: Read original manuscript6862 onward and6934 onward plus exact maximal-KS receipt. The existing classical invocation is not a Lean construction. Six new sources and primary QuaternionAlgebra API are bound. Exact rational closure/Gram/adjoint checks support implementation only; no local Lean or full arithmetic claim. Evidence: verification/consumer-source-pins.json; verification/primary-library-source-pins.json.

## Validation

Static closure:6 modules,0 accepted progress dependencies; all pinned Mathlib imports. Exact SymPy multiplication, Rosati, alternating adjoint, integral order closure and perfect Gram checks pass. The order basis has index20 over the naive basis and alternating determinant1. Reduced-trace determinant -44100 is supporting arithmetic, not a formal maximal-order or ramification classification. No local Lean; hosted kernel/recursive audit and independent bound review pending.
