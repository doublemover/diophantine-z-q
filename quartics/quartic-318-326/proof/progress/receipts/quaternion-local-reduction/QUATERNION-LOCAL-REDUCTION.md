# The actual quaternion maximal order modulo three

## Result and scope

Let B be the actual rational quaternion algebra of reduced discriminant210 used by the Shimura construction, and let O be its chosen maximal Z-order. There is a ring isomorphism

    O/3O  ≅  { [a b; 0 a^3] : a,b in F9 },

with F9 any fixed field of nine elements, in particular the literal Mathlib GaloisField(3,2) used in RamifiedResidueModel318. It is an isomorphism of the actual maximal-order reduction, not an assumption that an unrelated finite presentation models O.

This note proves that identification using the precise local classification/maximal-order theorem and an explicit valuation, basis and reduction calculation. It also checks the local-unit and full-level marking interpretation. These are classical local-division-algebra/abelian-variety theorem applications, not a Lean construction of the actual rational quaternion order or its completion. The downstream finite algebra, unit/scalar quotient and group-cardinality proofs are already kernel checked in level-three-kernel.

## 1. The source order at three is the unique division maximal order

Since3 divides210, B_3=B tensor_Q Q3 is a quaternion division algebra. The chosen global order is maximal. Maximality is local, including after completion, so O_3=O tensor_Z Z3 is a maximal Z3-order in B_3.

The exact primary input is John Voight, Quaternion algebras, stable author version1.0.5 dated10January2024:

- Lemma10.4.3 and §23.2.2: local/completed maximality;
- Lemma13.3.2 and Proposition13.3.4: the division valuation and its unique maximal valuation order;
- Theorem13.3.11(a,b): the unique local quaternion division algebra is (E,3 | Q3), with E/Q3 the unramified quadratic field, and its order is S+S*Pi;
- §23.2.5 restates that exact maximal-order description.

These apply to B_3 because Q3 is a nonarchimedean local field with finite residue field, and to O_3 because it is the completion of a maximal order. An algebra isomorphism from B_3 to this standard division algebra necessarily sends O_3 to its unique maximal order. No choice or assumption of a global integral basis of the original O is used to identify the local maximal order.

We give the coordinate/integrality argument explicitly below rather than using the theorem's lattice statement as an unexplained presentation.

## 2. Unramified quadratic field, uniformizer and integrality

Write E=Q3(i), with i^2=-1. The polynomial X^2+1 is irreducible and separable modulo3, so E/Q3 is the unramified quadratic extension and its integral closure S is Z3[i]. Its residue field k=S/3S has nine elements. The nontrivial automorphism sigma sends i to -i and reduces to the Frobenius a->a^3 on k.

The local classification provides a decomposition

    B_3 = E + E*Pi,    Pi*a=sigma(a)*Pi,    Pi^2=3.

One can start with Pi^2=3u for a unit u instead: surjectivity of the unit norm for the unramified quadratic extension allows multiplying Pi by an element of S^* to make its square exactly3. That rescaling does not change S+S*Pi. In either presentation, reduction modulo3 has the same multiplication.

Normalize the valuation v_E by v_E(3)=1. For nonzero a in E, the norm has v_3(N(a))=2v_E(a). For x=a+b*Pi the reduced norm is

    nrd(x)=N(a)-3N(b).

When both terms are nonzero their valuations have opposite parity: 2v_E(a) and1+2v_E(b). They cannot cancel. With the evident infinity convention when a or b is zero,

    v_3(nrd(x)) = min(2v_E(a),1+2v_E(b)),
    w(x) = (1/2)v_3(nrd(x)) = min(v_E(a),v_E(b)+1/2).

The factor1/2 is the normalized division valuation extending v_3. Because v_E takes integer values, w(x)>=0 holds exactly when a and b belong to S. Thus the unique maximal valuation order is exactly

    O_3 = S + S*Pi,

and its Z3-basis is 1,i,Pi,i*Pi. This is the required actual integrality statement. The formula also shows directly that the maximal ideal P consists of a in3S and b in S, that P=O_3*Pi, and that P^2=3O_3. In particular O_3/P=k, whereas O_3/3O_3 is the larger81-element ring. Confusing these two reductions would give the wrong level count.

For completeness, uniqueness/maximality can also be seen directly here: S+S*Pi is a rank-four Z3-order. Every element of any Z3-order is integral, hence its reduced norm is integral, so its w-value is nonnegative and the element lies in S+S*Pi. This is exactly the valuation-order argument in the cited proposition.

## 3. Exact reduction homomorphism and its kernel

Choose any field isomorphism k->F9. Such an isomorphism fixes F3 and commutes with Frobenius, so it preserves the multiplication below. For a,b in S define

    Phi(a+b*Pi) = [ abar  bbar; 0 abar^3 ].

Addition and the identity are preserved. The product before reduction is

    (a+b*Pi)(c+d*Pi)
      = ac+3b*sigma(d) + (ad+b*sigma(c))*Pi.

Modulo3 this becomes

    (abar,bbar)*(cbar,dbar)
      = (abar*cbar, abar*dbar+bbar*cbar^3),

exactly the checked triangular-matrix product in RamifiedResidueModel318.pair_mul. The map is surjective because a and b can independently lift any two residue elements. Its kernel is exactly3S+3S*Pi=3O_3, by the proved integral basis. The first isomorphism theorem therefore gives the required ring equivalence O_3/3O_3 with the constructed matrix model.

The global-to-local reduction is also exact. O is a finite torsion-free Z-module of rank4, hence free. In any Z-basis, completion is coefficientwise Z->Z3. Modulo3 the coefficient map Z/3Z->Z3/3Z3 is an isomorphism. Consequently the natural ring map

    O/3O -> O_3/3O_3

is bijective: its kernel before quotient is O intersect3O_3=3O, and every completed residue has integer coefficient lifts. Composing gives the displayed actual O/3O ring isomorphism. No unrestricted base-change assertion about a singular model is involved; this is a finite free lattice calculation.

## 4. Local units, scalar quotient and full level

Reduction sends O_3^* onto (O_3/3O_3)^*. Indeed an element of the matrix model is a unit exactly when its first coordinate is nonzero, as proved in LevelThreeKernel318. Any lift a+b*Pi of such an element has a in S^*, so the norm valuation formula gives w=0 and the lift is a unit of O_3. The reduction kernel on units is exactly1+3O_3. Thus

    O_3^*/(1+3O_3) ≅ (O/3O)^*,

which has72 elements by the actual finite-ring theorem. This statement concerns local units (and then adelic level units), not an unjustified surjectivity assertion for the global group O^*.

For the full principal level-three subgroup U(3), every other local component is O_p^*. Hence O-hat^*/U(3) is that entire72-element group. The diagonal rational scalars lying in O-hat^* are exactly {1,-1}, since their valuation at every finite prime is zero. Their reductions are distinct at3. The effective scalar quotient therefore has36 elements, exactly RamifiedResidueModel318.effective_card.

This uses the entire level cover. Restricting to norm-one/determinant-one markings or silently choosing one geometric component can instead produce18 and would not be the source construction. The reduced-norm multiplier is not to be removed in the full canonical PEL level problem.

## 5. Why this is the actual level-marking module

For the chosen characteristic-zero quaternionic surface A, its rational3-adic Tate module V_3(A) has Q3-dimension4 and carries B_3. Since B_3 is a division algebra of dimension4, V_3(A) has rank1 as a left B_3-module. Its integral Tate module is an O_3-stable full lattice in that rank-one module.

Such a lattice is free of rank1 over O_3. After identifying V_3(A) with B_3, choose a lattice element alpha of minimum division valuation; this minimum exists because the lattice is bounded and the valuation is discrete. Every x in the lattice satisfies w(x*alpha^(-1))>=0, hence x lies in O_3*alpha. The reverse inclusion follows from O_3-stability. Thus T_3(A)=O_3*alpha, and

    A[3] ≅ T_3(A)/3T_3(A) ≅ O_3/3O_3

as left O_3-modules. This proves the module statement needed to count the actual O-linear full level markings.

Endomorphisms of a rank-one left module act by right multiplication, so the natural marking-change group may be written as the opposite unit group. Inversion identifies a group with its opposite and preserves the central sign subgroup. This is only an action-convention change, not a cardinal correction. The finite theorem's unit quotient consequently applies in either convention.

Yuan's full level is the full O-linear marking, with the uniquely determined polarization and its similitude convention; it is not an extra determinant-one restriction. The absence of additional characteristic-zero stabilizers on X_210 is supplied by the earlier actual curve calculation (the Q(i) and Q(sqrt(-3)) elliptic cases are excluded by ramified primes5 and7 respectively). Therefore quotienting the marking changes by the actual scalar automorphisms is precisely the sign quotient used here.

## 6. Consumer and remaining formal boundary

The preceding argument supplies, at classical theorem-application scope, the actual ring equivalence required by

    RamifiedResidueModel318.normalizer_card_of_model
    RamifiedResidueModel318.galois_degree_of_model.

The actual canonical normalizer extension by W=(Z/2)^4 and its action on the whole regular fiber are constructed in the separate canonical-model producer. Combined with that extension, the now-identified level kernel has36 elements, giving576 without a supplied cardinality premise. The actual faithful commuting Galois-action theorem then gives the normal fiber field degree dividing576.

The Lean packet has constructed the finite algebra and proved its exact counts and group consequences. It has not yet constructed the actual number-field quaternion algebra, its maximal order/completion, the Tate lattice or canonical Shimura action in Lean. Their identification is proved here by the cited local theorem and the explicit integral/reduction argument. This distinction must remain visible in any assertion about formal GeometricRealization.

## Primary verification record

Fresh author source: https://jvoight.github.io/quat-book-v1.0.5.pdf, stable version1.0.5 dated10January2024, PDF SHA2567386db0c57915a099af2cf60042b5284a71309a3785a67b4aa0f76002053babc. Printed155,199,200,201 and367 were rendered and visually inspected (PDF pages175,219,220,221,387). These cover completed/local maximality, division valuation, uniqueness of the maximal order, and the exact unramified quadratic decomposition. The full PDF and extracted text are saved with these pages. The author's older Dartmouth URL returned404; no inaccessible source was treated as read.
