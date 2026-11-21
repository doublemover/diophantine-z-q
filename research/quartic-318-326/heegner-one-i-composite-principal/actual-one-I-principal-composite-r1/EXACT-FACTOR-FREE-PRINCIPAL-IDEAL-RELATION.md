# Exact factor-free principal ideal relation in the faithful λ quotient

Fix the actual d, F, λ and integral element a=W−169B from the
[first principal computation](../actual-one-I-principal-relation-r1/EXACT-FIRST-PROJECTED-PRINCIPAL-COEFFICIENT.md).
Its exact principal norm is ±3^29·13^333·5881·C, with the same
2379-digit unfactored integer C, coprime to 6·13·5881·d.
We recover the **entire residual ideal** of norm C without
factoring that integer. This completes one compressed projected
principal relation, not a class-group generating or saturation certificate.

## One composite residue homomorphism

Let f be the pinned 13-division polynomial in u=x(P)/d. In the
function ring of the untwisted model, multiplication formulas read

    x([k]P)/d = u − ψ_(k−1) ψ_(k+1) / ψ_k².

The product and square here are even in the untwisted y-coordinate,
so their right side lies in Q(u); the replay uses the exact same
division polynomials and relation y_untwisted²=u(u−1)(u+3).
Taking half the sum for k=1,…,6 gives the actual B=N_B(u)/D_B(u).
The numerator and denominator have degrees 72 and 71; the
integer equality used for local roots of a is

    H(u) = N_B(u)^2 − d·u(u−1)(u+3) D_B(u)^2 = 0.

Monic Euclidean division over Z/C succeeds for f and H without
a nonunit pivot. Its last nonzero polynomial is monic linear.
This gives the single root u_C, and the replay separately checks

    f(u_C)=0,  gcd(f′(u_C),C)=1,  gcd(D_B(u_C),C)=1,
    B_C=N_B(u_C)/D_B(u_C),  v_C=13u_C,  W_C=169B_C,
    W_C²=13 d v_C(v_C−13)(v_C+39),  gcd(W_C,C)=1

in the literal residue ring Z/C. Results for all coordinates
are frozen as exact integers. We do not assume C squarefree
or prime. A nonunit pivot would provide a partial factorization
or an exact algorithmic obstruction; neither is used here.

At every prime dividing C the displayed integral point-field
order is already maximal locally: the good-prime torsion
polynomial in v is étale and the quadratic radicand is a unit
at all its roots. Equivalently, at p not dividing 6·13·d,
the geometric nonzero 13-torsion and its free sign quotient
are finite étale, and their coordinates separate all labels.
Therefore the checked residue homomorphism extends to
O_F modulo C. Its kernel is the composite ideal

    I_C = (C, v−v_C, W−W_C),            Norm(I_C)=C.

The norm is C because the residue homomorphism is surjective
onto Z/C, constants mapping identically. It contains a since
W_C=169 B_C. At each rational p dividing C, the principal
ideal and I_C have the same p-part of their norm, and one
contains the other; hence their p-parts are equal as ideals.
This proves I_C gives exactly the complete residual support
and multiplicities of a, not merely a divisor of its norm.
The degree-one root means that each rational prime under I_C
has a single supported point-field prime of residue degree one;
it lies in a free Δ-orbit. No factoring is required for the equality.

## The exact projected relation and its limitation

The same calculation at the prime 5881 gives u=2185, B=2421,
v=4881, W=3360. The degree-one prime q_5881 at these coordinates
has multiplicity one in (a) by the exact norm. The norm-3
valuation proof previously gave coefficient 2 on the basis
generator eλ q_3, where q_3 is the specified norm-3 Tate orbit
representative. Its other relative 3-orbits, and both primes
over 13, have nontrivial stabilizers and are killed by λ.
Thus in the actual faithful quotient the complete compressed row is

    2 eλ[q_3] + eλ[q_5881] + eλ[I_C] = 0
                      in (Cl(F)/13)_λ.

Moreover C≡11 mod53 and C^4≡13 mod53, not 1, so C is not a
13th power. Since I_C has a single supported degree-one prime
over each rational p dividing C, its projected divisor is
nonzero modulo 13 (at least one exponent of C is not divisible
by 13 and the corresponding prime orbit is free). This is a
statement about the divisor, not nontriviality of its class.
In particular discarding I_C cannot be justified by pretending
there is no residual faithful support.

The single relation exactly eliminates one of its displayed
small generators in favor of the others, if using I_C as a
composite generator. It proves neither that the other generators
span nor that any of their global projected classes vanish.
No new global S-powerclass, class-rank bound, Selmer dimension,
rational rank, or point follows.

    sha256sum -c SHA256SUMS
    python3 -B check_composite_principal_support.py | cmp - EXACT-COMPOSITE-SUPPORT.json
