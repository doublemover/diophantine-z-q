# The actual marked Selmer-four lift can coexist with a nondegenerate two-dimensional block

Use the exact selected two-class family, normalized quotient V and true full marked-row proof in:
- note 7a597052 and manifest e649acb1 (two contact classes, with the same actual shallow scales and original index);
- note 864eda3e and manifest 92707c5c (all actual Kummer local conditions);
- note 9a9c8988871912e77ae9ce651c65331432b5988334751ddb0cdc0e7d2a50ac27, manifest 45899b89d72bec33bebdab8c3abb37855ef5618d5303a18e36d147291909dab5 (whole marked row).

Write a=p_a q_a, b=p_b q_b, D=ab, p_a=415721, p_b=9807649 and keep the orientation, saturation, sixteen earlier contacts, one common even index CRT and real constraint of those proofs. Fix the previously allowed q_a. There is a choice of q_b in this exact family for which the marked class α=(D,b,a) is in the image of Sel₄(E_D)→Sel₂(E_D), and the ordinary Cassels pairing on the normalized space V simultaneously has rank at least two. In particular its radical lies in codimension two and contains the marked line. No rank, numerical q_b, Sel₈ lift, rational point, all-factor completion or point on a joint extra-cover pullback is proved.

## 1. A genuine complementary block in the fixed space

The exact W local calculation gives the two elements

    U = (a,1,a),    V₁ = (1,a,a).

Both are fixed and already normalized at every admissible q_b, since a is a square there. In the Weil character coordinates of the actual full rational E_D[2] they are χ_a times two distinct nonzero geometric 2-torsion points (the points with bit triples 101 and 011). These points have Weil pairing 1 in additive notation. Their cocycle cup is therefore (g,h)↦χ_a(g)χ_a(h). The two classes are independent in the quotient by rational torsion since they are both normalized at q_b and a is nonsquare. Their span does not contain the normalized mark F_*=(t,aδ,atδ): the first coordinate of any element of their span is either 1 or a, whereas t has squareclass 2399, outside the support of a. Here δ=t−s uses the original same scaled roots.

## 2. A literal quartic governing bit

For each r in {p_a,q_a}, choose an order-four character of (Z/rZ)^× whose square is the quadratic character, which exists since r≡1 mod8. Their product gives a surjective additive character Ψ:G_Q→Z/4 with reduction χ_a. Write its two bits as Ψ=χ_a+2Γ with representatives 0,1 for each bit. Addition modulo four gives

    dΓ(g,h) = χ_a(g)χ_a(h).

Thus Γ is an exact primitive of the cup for U,V₁. It is unramified outside p_a,q_a and is a character on the kernel of χ_a. Since admissible q_b splits in Q(√a), the two local values Ψ_r(Frob_qb) are both even. Consequently (-1)^Γ(Frob_qb) is the product of the rational quartic-residue signs of q_b at p_a and q_a. No choice of order-four orientation matters on quadratic residues.

Apply [Smith, Lemma 3.1 and the proof of Theorem 3.2, eq. (3.3)](https://arxiv.org/pdf/1607.07860), with fixed elliptic curve E_(a p_b) and twisting values two admissible q_b. The ratio of the twist values is a square at all fixed bad places, at 2 and infinity, and at p_a,q_a,p_b, as in the fixed normalized quotient proof. The two normalized cocycles are trivial at both variable primes. The signed Artin sum of the two quadratic restriction values of Γ is the difference of their two pairing bits. Equivalently flipping just one of the two quartic signs flips CT(U,V₁). This is an application of the explicit carry primitive to the proof of the theorem, not the generic 32-degree four-character field formula.

## 3. The old CRT and order proof has both quartic choices

The old two-class procedure strips p_a and q_a from the index modulus when forming its finite level and then uses a separate Gaussian ray at the retained primes. At p_a the required norm is a square, and both split Gaussian residues must avoid the fourth roots of unity. For either nonzero chosen norm residue n, there are at most eight forbidden choices of the first component x in F_p_a^×: x∈μ₄ or n/x∈μ₄. Thus each required rational quartic phase can be attained without disturbing the requirement that both group orders be prime to p_a. The explicit two choices even use the same x=2:

    p     i (mod p)   n   x       n/x       Gaussian (r,s)
    415721  117278    1   2       207861    (311792,119902)
    415721  117278    9   2       207865    (311794,354458)

Their rational norms are 1 and 9 mod p_a. Their quadratic signs are both +, and the quartic signs are opposite (3 is a quadratic nonresidue). None of the four displayed split components is in μ₄. Multiplying by a Gaussian unit leaves the norm fixed and preserves this exclusion. At q_a use exactly the same Gaussian residue in both cases, so its quartic contribution is unchanged. Other residues are exactly the old choices. The same abelian ray disjointness and existing positive-density sieve apply separately to each ray choice. We only need two admissible references; no numerical prime is claimed.

The two references have opposite CT(U,V₁) by §2. Start from the one with CT(U,V₁)=1. Then run the exact whole marked-row proof with *this* chosen finite ray. Its central elements are products of commutators over Q(i); in particular they act trivially on the added abelian quartic field. The changed p_a ray is abelian and is the only possible ramification there on the respective stripped order component, so the two central-inertia calculations in the marked-row proof are unchanged. Prescribing the central shift of the chosen reference Frobenius annihilates the complete marked row and preserves CT(U,V₁)=1. The original infinite tail and the real-index conclusion apply with this fixed enlarged field, whose extra ramification is only at p_a and q_a already in the retained ray.

## 4. Exact implication and what remains

The block with basis U,V₁ is the hyperbolic alternating block; splitting it off leaves an alternating space of dimension dim V−2 containing the marked line in its radical. Since the pairing descends from Sel₂ after removing the two rational torsion Kummer rows,

    dim im(Sel₄(E_D) -> Sel₂(E_D)) ≤ dim Sel₂(E_D) − 2.

If it were separately proved that dim V=3, the marked line would be the entire normalized radical; that dimension is not established by the known-support relaxation. More generally this one block does not control the remaining fixed-support rank. Even a unique normalized marked radical line would still need a nonzero 2-infinity corank input (e.g. the correct odd parity) plus the external pointwise low-corank 2-converse to infer a rational point. A rational point on this two-factor genus-one cover would not by itself put its parameter in the prescribed neighborhoods or resolve other factors.

Signed: independent reviewer /root/high_review_ci. Mathematics and finite residue check; no Lean or remote action.
