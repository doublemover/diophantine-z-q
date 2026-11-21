# One unmarked ordinary genus-slice polynomial determines the live edge phase

This is an exact receiver for the more deeply normalized ordinary bit, not an evaluation. It uses only the reciprocal-\(j\) polynomial of **one actual full genus slice** and one coefficient of a quadratic-neighbor resultant. No marked level coordinates, independent edge orientation choices, or higher dyadic lifts enter the receiver. The unmarked polynomial of the **whole** Hilbert orbit is not an adequate replacement, and this note does not compute either original genus-slice polynomial.

Let \(n\equiv23\bmod24\) be positive squarefree as in the [maximal ordinary genus-depth theorem](../original-detectors-maximal-ordinary-genus-depth-r1/MAXIMAL-SPLIT-GENUS-ORDINARY-HEEGNER-DEPTH.md), and fix genuine CM inputs in one joint slice for its real genus characters split at both 2 and 3. Both horizontal ideal actions \(\mathfrak p_2,\mathfrak p_3\) preserve that slice. Reduce at a place above 2 and let
\[
              H(X)=\prod_{\text{slice}}(X-a),\qquad a=1/j .
\]
This is a squarefree polynomial over \(\mathbf F_2\) with nonzero constant term. Indeed the ordinary CM lifts have maximal order at the source and split \(\mathbf Z_2\times\mathbf Z_2\) action. The idempotents split the ordinary \(2\)-divisible group, giving the canonical lift by Serre--Tate; hence two characteristic-zero \(j\)'s cannot reduce to the same ordinary \(j\). The Frobenius action preserves the slice, and the unique supersingular \(j=0\) is excluded. The cyclic 3-neighbor with conductor increased by 3 also has the split \(\mathbf Z_2\times\mathbf Z_2\) action, since its conductor remains prime to 2. Its reduction and that ordinary canonical lift have the same prime-to-2 endomorphism ring. In particular its \(j\) cannot be one of these maximal-order roots; alternatively identical reductions would imply identical canonical lifts, whose characteristic-zero endomorphism orders are different.

In the ordinary characteristic-two chart of [Colò, Appendix A](https://www.leonardocolo.com/documents/thesis/PhD_Thesis.pdf), both ends of a degree-3 edge satisfy
\[
     a=\frac{u^3}{(u+1)^4},\qquad
     b=\frac{u}{(u+1)^4},\qquad ab=(a+b)^4 .
\]
The first map (equivalently the map to \(j_s\)) is étale of degree four at ordinary finite \(j\): at \(u\ne0,1,\infty\), differentiation of \(j_s=(u+1)^4/u^3\) is nonzero. The four neighbors have distinct \(b\), since \(a/b=u^2\). Their exact polynomial is accordingly
\[
                         Y^4+aY+a^4 .
\]
A source with maximal CM has exactly two horizontal 3-neighbors because 3 splits. Both are in the chosen slice and neither vertical neighbor is in it by the canonical-lift observation. These are geometric neighbors on the actual reduction, not a count of all roots weighted by a class multiplicity.

In the étale algebra \(A=\mathbf F_2[X]/H(X)\), define the monic degree-two polynomial \(G_X(Y)\) as the fiberwise greatest common divisor of \(H(Y)\) and \(Y^4+XY+X^4\). This is well defined over \(A\) by the preceding exact fiber-degree statement. It can be obtained by finite linear algebra without choosing a generator of each field factor: in the finite étale rank-four \(A\)-algebra \(A[Y]/(Y^4+XY+X^4)\), take the rank-two kernel of multiplication by \(H(Y)\), then the characteristic polynomial of multiplication by \(Y\) on that kernel. Put \(G_X(Z+X)=Z^2+C_1(X)Z+C_2(X)\). If \(Q_3\) denotes the class of a prime over 3, each orbit of \(Q_3\) on the slice is a closed undirected cycle of 3-edges. The two horizontal neighbors are distinct and neither equals the source, as shown by the quartic and \(ab=(a+b)^4\). The fixed level orientation takes each undirected edge exactly once around its cycle, independent of whether \(Q_3\) or \(Q_3^{-1}\) was used. There is no arbitrary separate choice of a perfect matching.

For each undirected edge \(\{a,b\}\) write \(w=a+b\). Both endpoints enumerate that same edge in the quadratic neighbor product, so
\[
  \operatorname{Norm}_{A/\mathbf F_2}
        (1+C_1(X)V+C_2(X)V^2)
      =\left(\prod_{\{a,b\}}(1+wV)\right)^2 .
\]
This identity preserves multiplicity when different edges have the same sum. The old edge statistic is the sum of \(w^5\), since \(w=T^{-1}=(t_3-1)^{-2}t_3\) in characteristic two. But
\[
  \sum_{\{a,b\}} w^3
    =\sum_{\{a,b\}}(a^3+b^3+ab(a+b))
    =\sum_{\{a,b\}}w^5
\]
because each vertex appears twice and \(ab=w^4\). Likewise \(\sum w=0\). Newton's identity in characteristic two therefore identifies this cubic power sum with the third elementary symmetric coefficient of the edge-sum polynomial. Thus the exact one-bit output is
\[
       [V^6]\,\operatorname{Norm}_{A/\mathbf F_2}
                      (1+C_1(X)V+C_2(X)V^2).
\]
In particular the norm need only be computed modulo \(V^7\); no ordered edge roster, square-root choices or full resultant coefficient table are required. This is a direct finite receiver once \(H\) is furnished. It neither obtains \(H\) at controlled cost for the literal detectors nor supplies any production bit.

