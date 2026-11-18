# Explicit descent of a degree-three cocycle through a normal subgroup

**Mathematical proof, not a Lean proof.** All coefficient arithmetic below is additive notation for an arbitrary abelian G-module A (in the local application A=L^×); thus zero means the multiplicative identity. No semidirect product or homomorphic choice of representatives is used.

**Input.** Let H be normal in G. Write Q=G/H. Let w be a 3-cocycle on G with w|H³=0. For every g assume a 1-cochain d_g on H with ∂d_g=S_g w, where t_g(a)=g⁻¹ag and
S_g w(a,b)=w(g,t_g(a),t_g(b))−w(a,g,t_g(b))+w(a,b,g).
Assume H¹(H,A)=0. Then w is cohomologous to the literal inflation of a 3-cocycle on Q with values in A^H. The proof produces the gauges; w is not presumed invariant in its arguments. The signs use
∂U(x,y,z)=xU(y,z)−U(xy,z)+U(x,yz)−U(x,y).

Choose a set-theoretic section s:Q→G and write x=s(q_x) h_x. The cases with x∈H are explicitly set to zero below; no normalization at the identity is required.

**1. Kill the last slot.** Set U(x,a)=−w(s(q_x),h_x,a) when x∉H and a∈H, and zero otherwise. For x∉H and a,b∈H, the cocycle equation at (s(q_x),h_x,a,b) gives ∂U(x,a,b)=w(x,a,b). For x∈H both vanish. Hence w₁=w−∂U vanishes on G×H×H.

Set V(x,y)=w₁(x,s(q_y),h_y) for y∉H, and zero otherwise. For a∈H and y∉H one has ∂V(x,y,a)=V(x,ya)−V(x,y)=w₁(x,y,a), by the cocycle equation at (x,s(q_y),h_y,a), whose first two terms vanish. For y∈H both sides vanish. Hence w₂=w₁−∂V vanishes on G×G×H. Its cocycle equation at (x,y,z,a) gives w₂(x,y,za)=w₂(x,y,z). Thus the last argument depends only on q_z.

**2. Identify and kill the middle obstruction.** Let B=U+V, so B|H²=0. Put L_g(a)=B(g,t_g(a))−B(a,g). Expanding ∂B at the three triples in S_g yields
S_g(∂B)(a,b)=gB(t_g(a),t_g(b))−B(a,b)−∂L_g(a,b)=−∂L_g(a,b).
Indeed g t_g(a)=a g and g t_g(b)=b g cancel the cross terms. Since the last slot of w₂ vanishes on H, S_g w₂(a,b)=w₂(a,b,g). Consequently
w₂(a,b,g)=∂(d_g+L_g)(a,b).
For each q≠1 choose f_q=d_{s(q)}+L_{s(q)}; choose f_1=0 since w₂(a,b,H)=0. Extend f_q by zero outside H to a function on G. Put W(x,y)=f_{q_y}(x). Then ∂W(x,y,a)=0 and ∂W(a,b,y)=∂f_{q_y}(a,b) for a,b∈H. Hence w₃=w₂−∂W has the same last-slot vanishing and is zero on H×H×G. It still depends only on q in the last slot, by its cocycle equation.

Put X(x,y)=−w₃(s(q_x),h_x,y) when x∉H, zero otherwise. It depends only on q_y and is zero when y∈H. For x∉H, a∈H, the cocycle equation at (s(q_x),h_x,a,y) and q_{ay}=q_y give
w₃(x,a,y)=w₃(s(q_x),h_x a,y)−w₃(s(q_x),h_x,y)=∂X(x,a,y).
For x∈H both sides vanish; ∂X(x,y,a)=0 for every x,y. Thus w₄=w₃−∂X vanishes whenever either of its last two arguments is in H. Its last argument depends only on its quotient; the equation at (x,y,a,z) then gives w₄(x,ya,z)=w₄(x,y,az)=w₄(x,y,z). Its middle argument also depends only on its quotient.

**3. Kill the first slot.** For any quotient pair q,r, the function a↦w₄(a,s(q),s(r)) on H is a 1-cocycle: evaluate ∂w₄ at (a,b,s(q),s(r)) and use the preceding two slot conditions. By H¹(H,A)=0 choose v(q,r) such that this value is a·v(q,r)−v(q,r). When q or r is the identity choose v=0. Take Y(x,y)=v(q_x,q_y). Its coboundary at (a,x,y) equals a·v(q_x,q_y)−v(q_x,q_y), and at (x,a,y) or (x,y,a) it is zero. Thus w₅=w₄−∂Y vanishes whenever **any** slot lies in H.

**4. Descend the actual arguments and values.** The same cocycle equations at (x,y,z,a) and (x,y,a,z) show quotient dependence in the last two slots for w₅. The equation at (x,a,y,z) yields w₅(xa,y,z)=w₅(x,ay,z)=w₅(x,y,z). Finally, at (a,x,y,z) it yields a·w₅(x,y,z)=w₅(ax,y,z)=w₅(x,y,z). This gives a well-defined cochain on Q³ with values in A^H; the G-action there factors through Q. It is closed, by evaluating its coboundary on representatives. In particular w=infl(w_Q)+∂(U+V+W+X+Y). The construction compares coefficients, all three argument domains, and the actual coboundary.

## Application to the finite tame local common field

Let D,I,K,F,J,N and i_j be as in the independently reviewed common-inertia packet. Start with a 3-cocycle on D in K^×. Use the cyclic subgroup primitive (Hilbert 90 plus cyclic periodicity in degree three) on I and extend its 2-cochain arbitrarily to D²; subtract its coboundary to obtain w with w|I³=0. Consequently its mixed cochains S_gw are closed (the slant differential is g applied to the conjugated restriction, minus the restriction). Apply the selected tame cyclic coefficient primitive construction to each of these |D| mixed cochains and the common-inertia theorem to this finite family.

Let G=Gal(N/F) and H=J. The actual map θ:G→D restricts on J to π:J→I. Put w'(x,y,z)=i(w(θx,θy,θz)) for the single old-field inclusion i:K→N. This is closed because inclusion is θ-equivariant and θ is a group map. Its restriction to J³ is zero. Since θ(x⁻¹ax)=θ(x)⁻¹θ(a)θ(x), direct substitution into the three-term formula gives
S_x w'(a,b)=i(S_{θx}w(πa,πb)).
The original common-inertia theorem provides d'_x(a)=i_{θx}(d_{θx}(πa)) with precisely this coboundary on J; each i_g restricts to the same i on K. Thus all elements of G are covered, not just chosen Frobenius lifts. This does NOT require the d'_x themselves to be equivariant under G. Hilbert 90 gives H¹(J,N^×)=0 since N/N^J is Galois with group J. Apply the four steps above.

Here Q=G/J is the Galois group of the residue extension, cyclic since the residue fields are finite; N^J/F is Galois with this full group. Cyclic cohomology periodicity and Hilbert 90 give H³(Q,(N^J)^×)=0. Therefore the inflated original 3-cocycle on G is a 3-coboundary after the documented finite tame-stage enlargement. This is NOT a claim that every local Galois extension has tame cyclic inertia, that the uninflated class was trivial at its old stage, or that global H³ or the rank bound follows.

**Inputs referenced.** Committed/recovered source names: ActualCasselsTateThreeConjugationHomotopy318 (`twist`, `slant`, `slant_differential`); ActualCasselsTateCyclicRestrictionNormalization318 (`normalize_cyclic_restriction`); ActualCasselsTateGeneralCyclicFieldPrimitive318 (`cyclic_field_three_boundary`); the selected coefficient primitive and 2026-11-18 COMMON-INERTIA.md. Standard residue Galois surjection: [Stacks, Galois extensions and ramification](https://stacks.math.columbia.edu/tag/09E3); finite cyclic groups use the usual two-periodic resolution. This result does not infer argument descent from the earlier invariant-value residual lemma; the five explicit gauges supply the missing argument.
