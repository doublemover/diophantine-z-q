# Exact separating character order on the original first arm

For either phase of the actual first balanced detector arm, every class character of order dividing eight misses the marked class \(\mathfrak B\). More sharply, let \(2^m\) be the order of the unique cyclic factor of order at least four in the \(2\)-primary class group of its imaginary quadratic field \(K\). Then the **minimal** class character order detecting \(\mathfrak B\) in \(L=K(\sqrt3,\sqrt{17})\) is \(2^{m+2}\), and that order is attained. The exact selectable quartic gate \(-1\) gives \(m=2\), so on that subfamily an unramified **cyclic-sixteen** detector exists and is optimal. There is no assertion about its value on the uncomputed signed Heegner ideal.

## 1. Four exact genus kernels on the same selected prime support

Take \(n=\beta q_0\prod I_j\) with \(u=1,\ v=\theta\), no repair prime and \(q_0\equiv7\bmod24\). All other primes in \(n\) are \(1\bmod8\); their residues modulo 3 are all \(1\) except \(17\equiv2\bmod3\). All are distinct, and the literal balanced selector and mark hold with either exact three/four-helper core. Write \(D=-n\), \(K=\mathbf Q(\sqrt D)\), \(F=\mathbf Q(\sqrt3,\sqrt{17})\), \(L=FK\). Use the four imaginary quadratic subfields
\[
 K_0=\mathbf Q(\sqrt D),\quad K_1=\mathbf Q(\sqrt{D/17}),\quad
 K_2=\mathbf Q(\sqrt{3D}),\quad K_3=\mathbf Q(\sqrt{3D/17}).
\]
These are the actual subfields, not a set of independently chosen imaginary twists. The defining radicands are odd and squarefree. The first two are \(1\bmod8\); the last two are \(3\bmod8\), so their rational 2-adic field is \(\mathbf Q_2(\sqrt3)\). Exactly the last two ramify at 2 and 3.

For each \(K_j\) consider a quadratic unramified ideal-class character that is trivial on **every rationally ramified prime ideal** of \(K_j\). Such a character descends from \(\mathbf Q(\sqrt A)\): conjugation acts by inversion because rational ideals are principal, and a quadratic unramified extension stable under conjugation is biquadratic over \(\mathbf Q\), since true complex conjugation has order two and is nontrivial on \(K_j\). The rational squareclass \(A\) has odd support only at primes ramified in \(K_j\). Normalize its \(q_0\)-bit to zero by multiplying by the defining radicand; this does not change the extension over \(K_j\).

Here is the exact dyadic condition, including the two additional fields. For \(K_0,K_1\) the field splits at 2 and an unramified auxiliary \(A\) with \(q_0\)-bit zero is positive (the negative of a product of the remaining \(1\bmod8\) primes is the ramified \(-1\) class). There is no 2-bit. For \(K_2,K_3\), the prime over 2 is ramified and its ideal must have trivial character, so the extension is **split** over \(\mathbf Q_2(\sqrt3)\). The only rational squareclasses that become square there are 1 and 3. This again excludes a 2-bit. After the \(q_0\)-normalization the possible odd \(A\) have 2-adic class \((-1)^s 3^b\), with \(b\) its optional 3-bit, so the requirement is exactly \(s=0\), with \(b\) still free. In particular one cannot treat the added 3 direction as merely another symmetric old odd vertex.

Let \(S_j\) be the odd ramified support of \(K_j\) obtained by removing 17 and/or adding 3 from the base support. Let \(x_p=v_p(A)\bmod2\) on \(S_j\), \(x_{q_0}=0\). At any odd \(p\in S_j\), the character at its ramified ideal is the symbol of the **stripped unit** \(A/d_j^{x_p}\), where \(d_j\) is the defining radicand of \(K_j\). Thus row \(p\) of the trivial-character test is
\[
  \sum_{q\in S_j,\ q\ne p} \ell_{pq} x_q
   +x_p\left(\sum_{q\in S_j,\ q\ne p}\ell_{pq}+\kappa_p\right)=0,\qquad
  \ell_{pq}=\operatorname{bit}(q/p),\quad
  \kappa_p=\operatorname{bit}(-1/p).
\]
The added diagonal \(\kappa_p\) records the minus in the negative radicand on a ramified \(A\)-row; it matters at 3 and the \(q_0\) bit is zero. At all other finite places (outside 2 and the odd ramified list) the auxiliary squareclass is a unit and unramified, so this test is complete.

The row-denominator, column-numerator bits come exactly from the two published deleted sharp arrays. In the base arm the retained \(\lambda\) has only its 17 bit, so flip the 17-diagonal to recover the deleted ordinary matrix. Recover the omitted \(q_0\)-entries by the full row-sum condition; the old off-diagonal symbols are symmetric because \(q_0\) is the sole \(3\bmod4\) prime of \(n\). For 3, the only nonzero old incidences are
\[
 \ell_{17,3}=\ell_{3,17}=1,\qquad
 \ell_{q_0,3}=1,\quad \ell_{3,q_0}=0 .
\]
The exact replay enumerates the full four small systems in either phase, including the \(q_0\) row, the 3 row when applicable, and the deleted column:
\[
 \begin{array}{c|cccc}
       & K_0 & K_1 & K_2 & K_3\\ \hline
 \text{ramified-prime annihilator} &
       \langle\chi_\beta\rangle & 0 & 0 & 0 .
 \end{array}
\]
Here the only nonzero mask for \(K_0\) is 127, the actual full \(\beta\)-indicator in the old support order. The others' zero kernels do not mean their class groups are trivial; they mean no quadratic character can be the square of a nontrivial order-four character. Indeed that square would kill every ideal class of order dividing two, and in particular every ramified prime ideal class. Thus each of \(K_1,K_2,K_3\) has \(2\)-primary exponent at most two. Likewise \(K_0\)'s \(2\)-primary group has at most one cyclic factor of order at least four.

There is one such factor for \(K_0\). Write \(\mathfrak A_\beta\) for the product of its ramified prime ideals above \(\beta\). Its class maps under ideal extension \(j_0\) to the nontrivial marked class \(\mathfrak B\) of \(L\) (the 17 factor becomes principal via \(\sqrt{17}\)). The exact norm conic \(N_{K_0/\mathbf Q}(\alpha)=\beta\) gives \([\mathfrak c_K]^2=[\mathfrak A_\beta]\), as in the octic-gate paper. Hence \([\mathfrak A_\beta]\) is a nontrivial square of order two. If the sole large cyclic factor has order \(2^m\), \(m\ge2\), then this class is its unique nontrivial order-two element; ideal extension \(j_0\) is injective on that cyclic factor. The character \(\chi_\beta\) is exactly the primitive parity character of that factor, trivial on the remaining order-two part.

## 2. Exact norm identity, image and separating order

For each \(K_j\) let \(N_j:\mathrm{Cl}(L)\to\mathrm{Cl}(K_j)\) be ideal norm and \(j_j\) ideal extension. Use additive notation for class groups in the following identities. As endomorphisms of \(\mathrm{Cl}(L)\),
\[
 \sum_{j=0}^3 j_jN_j=4\,\mathrm{id}.\tag{1}
\]
Indeed the norm-extension operator for \(K_j\) is \(\sum_{g\in\mathrm{Gal}(L/K_j)}g\). In the four imaginary quadratic characters of \(\mathrm{Gal}(L/\mathbf Q)\cong C_2^3\), \(c\) (complex conjugation) has sign minus and hence coefficient zero in that sum; \(1\) has coefficient four. Each \(g\ne1,c\) appears twice, because exactly half of the four characters are trivial on it, and these terms cancel in \(g,cg\) pairs. Complex conjugation acts by inversion on \(\mathrm{Cl}(L)\) since its fixed quartic \(F\) has class number one. The eight group-ring coefficients are also checked by the replay; this does not assume a norm surjectivity theorem.

Now restrict to the \(2\)-primary subgroup \(G_2\) of \(\mathrm{Cl}(L)\). Norms into each of \(K_1,K_2,K_3\) have exponent at most two. Hence
\[
             8x=2j_0N_0x\qquad(x\in G_2).\tag{2}
\]
In particular the exponent of \(G_2\) divides \(2^{m+2}\). Multiplying (2) by \(2^{m-2}\) gives the exact marked-class relation
\[
             2^{m+1}x
       = \operatorname{bit}\!\left(\chi_\beta(N_0x)\right)\,[\mathfrak B].
       \tag{3}
\]
Here a \(+1\) character bit is zero, and a \(-1\) bit is one. The identity follows since \(2^{m-1}\) on \(\mathrm{Cl}(K_0)(2)\) reads precisely the primitive parity of its one large cyclic factor times its involution \([\mathfrak A_\beta]\).

The character \(\chi_\beta\circ N_0\) is **nontrivial**: it is the unramified base change of \(K_0(\sqrt\beta)/K_0\), and \(K_0(\sqrt\beta)\not\subset L\). For the latter, rational squareclasses inside \(L\) are generated by \(D,3,17\). Without \(D\) none contain the six genuine \(\beta\) primes; with \(D\) they contain the fresh \(q_0\), absent from \(\beta\). Thus \(L(\sqrt\beta)/L\) is a genuine quadratic extension, unramified by base change, and Artin reciprocity supplies a class at which its character is nontrivial. A quadratic character kills the odd-order subgroup, so it is already nontrivial on \(G_2\). This supplies the needed norm parity without computing a high-order ideal class or assuming the full norm map is onto.

It follows from (3) that the image of multiplication by \(2^{m+1}\) on \(G_2\) is exactly \(\{0,[\mathfrak B]\}\). Together with the upper bound, this proves that \(G_2\) has exactly one factor of order \(2^{m+2}\), all others smaller, and that \([\mathfrak B]\) is the involution of that maximal factor. Thus no character of order dividing \(2^{m+1}\) detects \(\mathfrak B\), while a character of order \(2^{m+2}\) does. More precisely the written quadratic character \(\chi_\beta\circ N_0\) has an unramified lift \(\Psi\) of exact order \(2^{m+2}\) with \(\Psi^{\,2^{m+1}}=\chi_\beta\circ N_0\), and every such lift detects \(\mathfrak B\). This uses the elementary cyclic-factor character construction; it gives existence of the appropriate Artin character, not an explicit defining polynomial for its field.

## 3. A selected subfamily of exact order sixteen

The exact quartic product from the octic gate is \(\chi_\beta(\mathfrak c_K)\), where \(\mathfrak c_K\) has class of exact order four. If it is \(-1\), that class has odd coordinate in the unique large cyclic factor of \(\mathrm{Cl}(K_0)(2)\), hence that factor itself has order four: an element of order four in a larger cyclic factor has even coordinate. Thus \(m=2\), and the minimum separating order in \(L\) is exactly sixteen. The order-sixteen lift exists on every member of this selected gate-\(-1\) subfamily. This answers the octic sufficiency question negatively even there. If the gate is \(+1\), the order-four class has even coordinate and squares to the same nontrivial involution, so \(m\ge3\) and the minimum is at least thirty-two, with the exact formula still \(2^{m+2}\).

The final-prime refinement achieving either gate can retain all old CRT rows, both original Selmer eights, the literal \(b\), and the separate simple level-48 CM intersection at 17. No cardinality is inferred for the entire class group. The actual relative **Heegner** sign ideal is still either \(1\) or \(\mathfrak B\) on this arm; certifying which by this now guaranteed optimal character (or by a direct invariant-ideal relation) remains an independent unknown. No trace nonzero, \(m\) for an unrefined individual selection, rank, or rational point is claimed.

### Exact dependencies and replay

- *Companion theta paired selection*, exact published paper **21c692023d5085335ff0ff4a31a943906acd27dc44549560fe63e2f86431fd9f**, §2 supplies the literal old plus and minus matrices and row-versus-column Legendre direction.
- *Ordinary genus characters cannot see the marked relative ideal class*, exact paper **9ebfd5382aca7956109e91584026cf5a43444aaf2902d46e64c42c845c1341ef**, supplies \(\mathrm{Cl}(F)=1\), the nontrivial marked class and quadratic descent.
- *A controllable quartic-residue gate for the first-arm octic character*, exact paper **99e92566809129e75005b968fa28e0a1409f9650c2e611e782b43e078cb4844b**, supplies the rational conic square root, the exact quartic product, and the selectable shared \(q_0\) refinement. The expression "octic gate" refers to the formerly necessary condition, not to an octic sufficiency result.

    python3 -B replay_four_imaginary_genus_kernels.py | cmp - EXACT-FOUR-IMAGINARY-GENUS-KERNELS.json
    sha256sum -c SHA256SUMS
