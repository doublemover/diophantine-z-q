# All primes above 11 and the four quadratic ideal projections

For the fixed bounded control \(D=-311,\ n=241\cdot311\), this supplement resolves the **entire 11-supported component** of the oriented CM-ratio ideal. At the four primes of \(E=\mathbb Q(\sqrt5,\sqrt6,\sqrt{-n})\) the exponents are \((-20,+20,+20,-20)\) in the named order below. Of the four binary projections, only the one in \(\mathbb Q(\sqrt{-5n})\) is nonzero at 11. This computes no other prime and no complete fractional ideal or residue at 29. It is not a computation on an original detector discriminant.

## 1. A second exact coefficient place, leaving the moving geometry fixed

The previous exact named calculation gives \(v_{\mathfrak P}(R)=-20\) for
\[
 \sqrt5=4,\quad\sqrt6=5s,\quad\sqrt{-n}=5,\quad s^2=2
 \qquad(\bmod 11).
\]
The named moving roots \(\sqrt D=2s,\ \sqrt{241}=4s\) and the actual ordered 16/3 roots \(2,0\) are fixed throughout. This sets the same actual 4598 moving arcs and the same absolute quadratic Gauss signs as the prior proof. Only the evaluation of the eight fixed real CM packets changes.

At the other coefficient embedding over the same positive named \(\sqrt{-n}\) root, replace the calibration primitive generator \(A\) by \(i/A\) and leave \(i,\sqrt2,\sqrt3\) unchanged. Indeed \(A^4+4A^2-1=0\) gives \((i/A)^2+2=-(A^2+2)\); thus this change flips \(\sqrt5\) and retains \(\sqrt6\). It is an actual Galois automorphism of the fixed point-coordinate fields, not a sign change to an individual coefficient or a different moving branch. Its residue \(A\) is \(4\bmod11\) instead of \(s\).

The checker performs both fixed-packet evaluations on each actual arc after the same marked Vélu quotient and checks every first-place row against the exact donor. At the second embedding exactly 3002, 1556, 26 and 14 arcs have largest factor depth 1, 2, 3 and 4 respectively, with no depth reaching the precision 5. The raw two signed-half totals are \(+10\) for \(\chi=+1\) and \(-10\) for \(\chi=-1\). Thus the second exact oriented valuation is \(+20\); it is not inferred by guessing the data reverse.

## 2. The four primes and the pushed valuations

At 11 the field \(E\) is unramified, and Frobenius flips only \(\sqrt6\), since 5 and \(-n\) are squares and 6 is a nonsquare modulo 11. Hence each residue degree is two, and signs of \(\sqrt5,\sqrt{-n}\) label four distinct primes. There are no further choices of prime associated to swapping the two residue representatives of \(\sqrt6\). Complex conjugation fixes the real field and sends \(R\) to \(R^{-1}\). This follows from the exact Fricke inversion of the eight-packet function and reindexing the two genus halves with \(\chi(\mathfrak n)=+1\) for the norm-48 ideal. Thus it supplies the remaining two exponents, not another unverified numerical lift:
\[
\begin{array}{c|rr}
 &\sqrt{-n}=5 &\sqrt{-n}=-5\\ \hline
 \sqrt5=4&-20&20\\
 \sqrt5=-4&20&-20
\end{array}
\]

For \(j\in\{1,5,6,30\}\) set \(M_j=\mathbb Q(\sqrt{-jn})\) and \(R_j=N_{E/M_j}(R)\). The ideal norm exponent at a binary prime is the sum of the exponents above it weighted by their relative residue degrees. The split binary fields \(M_1,M_5\) each have relative residue degrees two here; \(M_6,M_{30}\) are inert, with one prime and relative residue degree one. For \(M_1\), the two exponents above each given \(\sqrt{-n}\) root cancel. For \(M_5\) the product of the named roots \(4\cdot5\) is \(9\bmod11\). The two primes above that root both have exponent \(-20\), so this binary exponent is \(-80\); its conjugate root is \(2\bmod11\) and has exponent \(+80\). The inert primes in \(M_6,M_{30}\) have exponent zero, either by summing the table or by the conjugate-inverse identity for \(R_j\). Thus precisely one projected 11-component is nontrivial:
\[
   (R_5)_{11}=\mathfrak p_{9}^{-80}\,\mathfrak p_{2}^{80},
   \qquad (R_1)_{11}=(R_6)_{11}=(R_{30})_{11}=1.
\]
The subscript denotes the 11-supported part of the ideal, not a generator statement for that part.

The attached exact rows retain both valuation and largest depth per moving arc. Run sh verify.sh to check hashes, compare the earlier entire coefficient projection and recompute the four binary totals. Run sh verify.sh --all for the complete both-place geometry and depth check with Python 3 and python-flint 0.9.0. This never constructs an ideal at an unrelated prime or recovers a full CM product.
