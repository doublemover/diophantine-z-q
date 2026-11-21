# One unweighted quartic residue detects the actual first-arm mark

The exact coherent first-arm Heegner-quarter mark can be tested from a **single unweighted CM product** modulo one of the old helper primes. This is an equivalent aggregate, not its evaluation. It requires neither an oriented global ideal, a class group computation, all-place factorizations, nor the signed genus class labels. It keeps the same actual first twist and its two coherent phase comparisons.

## 1. An exact square in the real quadratic field

Keep the actual first-arm definitions of $L,J,E,D,n,\beta$ and $U_{\rm good}$ from the quartic-subfield result, in particular $E=\mathbf Q(\sqrt3)$ and $J=E(\sqrt{D/17})$. Let $P_{\mathfrak a}$ be the raw individual level-48 CM point on $E_0$, not its quarter. Put
$$
 h_T(P)=\frac{y(P)}{x(P)-3}-(2+\sqrt3),\qquad
 M_+=\prod_{\chi_{17}(\mathfrak a)=+1}h_T(P_{\mathfrak a}),\qquad
 S=\prod_{\mathfrak a}h_T(P_{\mathfrak a}).
$$
The element $M_+$ is in $L$. Its complex conjugate is the complementary half product because the level involution on indices has genus sign minus and $h_T(T_3-P)=h_T(P)$. The automorphism $\tau$ fixing $K(\sqrt3)$ and negating $\sqrt{17}$ sends it to the very same complementary half product. Hence $c\tau$ fixes $M_+$ and $M_+\in J$, with $S=M_+\bar M_+$.

Use the exact fourth-root product $C_4\in K(\sqrt3)$, normalized by the rational quarter and the dual cyclic-four kernel as in the relative sign theorem. The normalization of the good ideal divides its norm-one element by a factor $\alpha/\bar\alpha\in K^\times$ supported at 2 and 3. Thus
$$
 V=M_+U_{\rm good}
   =\frac{C_4}{12^{h/8}(\alpha/\bar\alpha)}
   \in J\cap K(\sqrt3)=E .
$$
Taking the norm of the first equality to $E$, with $N_{J/E}(U_{\rm good})=1$, gives the **exact** equality $S=V^2$. There is no unknown real unit multiplying that square. No computation of $\alpha$, $C_4$, or a square root of $S$ will be needed for the final residue test.

## 2. The unsigned exponents agree with the principal square-root ideal

Choose a literal old helper $I$ as in the quartic-subfield character theorem and an $E$-prime $\mathfrak i\mid I$. Its totally positive generator $t$ has $N_{E/\mathbf Q}(t)=I$; choose the unit factor $2+\sqrt3$ if necessary to make $E(\sqrt t)/E$ unramified at 2. Multiplying its initial generator by $-1$ if needed makes it totally positive; this does not change an unramified dyadic class because $-1$ and 5 give the same squareclass in $E_2$. The resulting character of $J(\sqrt t)/J$ detects the same mark as in that theorem.

For an unramified rational $p>3$, $p\ne17$, the integer valuation of $V$ at an $E$-prime is the unsigned total marked length at any chosen place above it: the divisor of $h_T$ has order two at $T$ and the product $S=V^2$, with no cusp intersections or vertical contribution. The order of $U_{\rm good}$ at an unramified prime of $J$ is the signed version of that sum, hence has the same parity. If the $E$-prime is inert in $J/E$, the norm-one condition forces the signed sum zero and the valuation of $V$ is even. If it ramifies in $J/E$, its underlying rational prime divides $n/17$ and has no collision on the first arm, since it splits in the fixed CM field. The valuation is zero there. At 2 and 3 every $h_T(P_{\mathfrak a})$ is a unit by the exact eta normalization of the marked product, so $V$ is a unit there too.

At the rational prime 17, each actual collision has length $1/2$ normalized over $\mathbf Q_{17}$. Thus $v_{\mathfrak p}(V)$ at the unique $E$-prime above 17 is half the total number of collision indices. The signed exponent of $U_{\rm good}$ in $J$ is half the difference of the two genus counts. These two half-integers agree modulo two as **integers** as follows. The nonzero-$k$ terms occur in pairs within the same genus, so contribute an even number to each count. For $k=0$ use two distinct old helpers (there are at least three), each with $(17/I_i)=-1$. The exact Eisenstein-factor switches at these two helpers commute on the integer $\gamma$ of norm $n/17$, preserve the **same** ordered level flags, and independently change which of two split factors occurs at their respective rational prime. The norm $n/17$ is squarefree, so this is a free group of four permutations on the $k=0$ indices. Each switch flips $\chi_{17}$; hence each orbit has two indices of each genus. Both full genus counts are even. It follows that taking their difference or sum after division by two gives the same parity. Here 17 splits in $J/E$, since $D/17$ is a rational unit and becomes a square in the unramified quadratic $E_{17}$.

Consequently the class-character product on a split half of $(U_{\rm good})_J$ is exactly the quadratic Artin product on the principal ideal $(V)$ in $E$ away from $\mathfrak i$. For split pairs this uses the same character on either member; for inert and ramified primes the preceding paragraphs show that the extra exponents in $E$ contribute nothing. At $\mathfrak i$ itself $V$ is a unit by no collision.

## 3. Reciprocity turns the product into one residue

The extension $E(\sqrt t)/E$ is unramified at dyadic places, at every other odd prime except $\mathfrak i$, and at both real places by total positivity. At $\mathfrak i$ it is the tame ramified quadratic extension. The product formula for $(t,V)$ gives
$$
 \chi_t(\mathfrak b_J)
   =\prod_{\mathfrak p\ne\mathfrak i}
       (t,V)_{\mathfrak p}
   =(t,V)_{\mathfrak i}
   =\left(\frac{V\bmod\mathfrak i}{I}\right).
$$
Here the real factors equal one; an unramified local factor is the quadratic residue symbol of $t$ raised to the ideal valuation of $V$, and the final tame formula uses $v_{\mathfrak i}(t)=1$, $v_{\mathfrak i}(V)=0$. The residue field is literally $\mathbf F_I$. Using $S=V^2$ and $I\equiv1\bmod4$, the desired test is
$$
 \boxed{\quad
      \chi_t(\mathfrak b_J)
        = \left(S\bmod\mathfrak i\right)^{(I-1)/4}
        \in\{1,-1\}. \quad}
$$
No root choice or unit ambiguity remains. Either oriented $E$-prime over the chosen helper works: run the exact generator proof with that prime. The resulting sign is the same mark, since either quadratic detector sends $\mathfrak B_J$ to $-1$.

The single input on the right is the reduction at a good prime of the **unweighted** product of all original level-48 values $h_T$; multiplicity of CM indices must be retained even if their geometric reductions coincide. Equivalently it is a product on the normalized marked supersingular quotient at the ramified prime $I$, because the original moving CM has ramified $I$ and the fixed $-192$ divisor is ordinary there. No signed genus class, number-field class group, raw intersection ideal, or global factorization is needed to run this receiver. The unweighted product is still not evaluated for a literal numerical original detector. Opposite phase (output $-1$) would give the actual first-arm point after the rational torsion correction; output $+1$ is only the eighth-division case of the trace, not a rank statement.
