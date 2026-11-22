# The actual compact Abel good target: full factorial fibre and null complement

Fix the actual filled fine-level complex curve \(X=X_1(M)(\mathbb C)\), in its already compared original period charts, and its own algebraic Jacobian \(J_X\). The curve is smooth, connected and projective, of genus \(g\). Use the same pointed degree-one Abel map \(a:X\to J_X(\mathbb C)\), actual exponential \(q:V=\mathbb C^g\to J_X(\mathbb C)\), its kernel lattice \(L\), and the unnormalized Haar measure \(\nu\) descended from Lebesgue measure on \(V\) in the actual invariant differential basis. The previously compared pullbacks are \(f_i(\tau)\,d\tau\). For a fixed lift \(c\) of the Abel value at \(i\), and primitives \(\Phi_i\) with \(\Phi_i(i)=0\), the already compared ordinary formula is
\[
 a(\iota(\Gamma_1(M)\tau))=q(c+\Phi(\tau)).
\]
Here \(\iota\) is the original ordinary-chart inclusion. The proof does not replace the Abel map by one into another torus or a QM surface.

Let \(A:X^g\to J_X(\mathbb C)\) be the Abel sum on the **ordered** product. Let \(D\subset X\) consist of the actual cusps and the actual two finite fibres above \(j=0,1728\). Let \(Q\subset X^g\) consist of those tuples with at least one entry in \(D\). Let \(R\) consist of the ordinary tuples outside \(Q\) having a lift \((\tau_j)\) with \(\det(f_i(\tau_j))\ne0\). Define
\[
 G=J_X(\mathbb C)\setminus A(X^g\setminus R).
\]
In particular **all** preimages of any \(y\in G\) lie in \(R\). This is not merely the image \(A(R)\).

## 1. Nullness without any cusp differential charts

Choose \(u_d\in V\) with \(q(u_d)=a(d)\) for each actual point \(d\in D\). Each tuple in \(Q\) determines a nonempty set \(S\subset\{1,\ldots,g\}\) of pinned positions and a label \(d_j\in D\) for each \(j\in S\). There are finitely many such masks. For a fixed mask take the map on *all* of \(\mathbb H^g\)
\[
 F_{S,d}(\tau_1,\ldots,\tau_g)
   =\sum_{j\in S}u_{d_j}+\sum_{j\notin S}(c+\Phi(\tau_j)).
\]
The unused coordinates \(\tau_j\) for \(j\in S\) may be set to \(i\). Every tuple with that mask has Abel value in \(q(F_{S,d}(\mathbb H^g))\), by exactly the original formula on the unpinned entries. The complex derivative of \(F_{S,d}\) has a zero column for each \(j\in S\). Its whole image is therefore a set of critical values of a smooth map on an open subset of real dimension \(2g\) with real target dimension \(2g\), and is Lebesgue-null by Sard. A null subset of \(V\) has null \(q\)-image for the same Haar measure: cover \(V\) by countably many sufficiently small translated injective quotient charts in which \(\nu\) is literally pushforward Lebesgue measure, or use the equivalent half-open lattice-domain construction. This argument does not require that the unpartitioned image is Borel; outer measure zero suffices. Thus \(\nu(A(Q))=0\), with no differential, parameter or analytic estimate at a discarded point.

On the unmasked ordinary chart the derivative is precisely \((f_i(\tau_j))\), with columns indexed by the original ordered variables. The zero determinant locus also has null image by the same Sard and Haar arguments. A tuple outside \(R\) is either in \(Q\) or is ordinary critical: the actual filling guarantees that each entry outside \(D\) has an original \(\mathbb H\) representative, and any such lift must be critical by the definition of \(R\). Hence \(\nu(G^c)=0\).

The original ordinary period projection is open, hence so is its finite product. The determinant is continuous and \(Q\) is closed as a finite union of inverse images of \(D\). Thus \(R\) is open. The image of its closed complement is closed because \(X^g\) is compact and the actual target is Hausdorff. This gives the genuine **open** \(G\) needed by the counted-measure theorem.

## 2. A single genuine Jacobi-inversion input gives the full degree

Let \(s:X^g\to\operatorname{Sym}^g X\) be the actual reordering quotient. On complex points its fibres consist exactly of the orderings of one effective divisor, with multiplicities. The map descending \(A\) is \(b:\operatorname{Sym}^g X\to J_X\), \(D'\mapsto[D'-gP_*]\), for the **same** point \(P_*\) as in \(a\). Its birationality for \(g>0\) is [Milne, *Jacobian Varieties*, §5 Theorem 5.1(a)](https://www.jmilne.org/math/articles/1986c.pdf). For \(g=0\) the same Jacobian is the point, the source \(X^0\) is the point, and the degree is \(0!=1\).

For \(g>0\), choose a nonempty source isomorphism locus \(U_0\) for the birational map. Remove the repeated-point locus (and optionally the closed locus of divisors containing any point of \(D\)) to obtain an open \(U\subset U_0\). It is nonempty: \(\operatorname{Sym}^g X\) is irreducible of dimension \(g\) and each removed incidence has dimension at most \(g-1\). The **whole** image of \((\operatorname{Sym}^g X)\setminus U\) under \(b\) is closed, by properness, and has dimension at most \(g-1\). Remove this image in the target. The resulting dense Zariski open \(W\) has precisely one full effective-divisor solution at each point: there is a solution by surjectivity (proper with dense image); all solutions lie in \(U\), on which the map is injective. This divisor is reduced and has exactly \(g!\) orderings. Thus we count the full ordered fibre of \(A\) on \(W\), not a selected branch.

Only analytic *density* of \(W(\mathbb C)\) is needed. A proper algebraic closed subset of the connected smooth complex variety \(J_X\) has no analytic interior. Each preimage of any \(y\in G\) has invertible complex derivative on an actual ordinary branch. The original local inverse charts then make \(A|_{A^{-1}G}\) locally a homeomorphism. Compactness of the full source makes it a covering over \(G\): the full fibre over \(y\) is closed, discrete and compact, hence finite. Choose pairwise disjoint local chart neighborhoods of its points. By avoiding the image of their closed complement, one obtains a common target neighborhood which those charts exhaust. This applies to an empty fibre too, with a neighborhood avoiding the image. Every evenly covered open neighborhood of any \(y\in G\) meets \(W(\mathbb C)\). Its true trivialization identifies the entire fibre over \(y\) with the entire fibre over such a generic point, proving exactly \(g!\) for \(y\). Neither connectedness of \(G\) nor regularity of any chosen arithmetic \(j=1\) tuple is asserted.

## 3. Exact native boundary

* The frozen-slot Sard producer uses the existing exact complex-derivative-to-measure-zero lemma. The actual-filled specialization adds the literal actual discarded set, original open projection and compactness; it requires no derivative chart at a discarded point.
* The point-level symmetric module uses the **literal** reordering quotient of \((\mathrm{Fin}\ g\to X)\). One genuine effective solution and reducedness give the ordered factorial count, and analytic density plus actual covering propagate it to every good fibre. Repeats on the literal good open are separately excluded by the original derivative: if two ordinary coordinates represent the same point, a holomorphic \(\Gamma_1(M)\) coordinate change relates their two derivative columns by a nonzero factor. Nonzero determinant precludes that.
* The remaining *new* native geometric seam for the degree is narrow: supply the dense-locus unique full effective-fibre property for the actual same-basepoint symmetric Abel map. Point-level reordering and covering alone do not establish it. A native form of the true algebraic degree-\(g\) Jacobi inversion theorem (or a genuine Picard/Abel theorem on the same input \(J_X\)) is sufficient. The earlier compact analytic-to-algebraic comparison and genuine invariant readout remain dependencies; they are not claimed repeatedly as new native constructions.
* The exact green Volume32r5 measure result already turns \(G\), its null complement, the actual measured local sheets and the full ordered cardinality into the determinant/Haar-volume equality. No numerical center selection, scalar base change, global height theorem or end-to-end native proof is claimed here.
