# Exact good-prime oriented valuations for the fixed-241 receiver

Fix one actual odd target \(E_n\) of the protected original fixed-103 and fixed-241 detector selector. Use its primitive fixed-conductor interpretation \(D=-m=-n/241\), and the corrected real CM-supported function \(\mathcal U\) (checksum-list c763e955648ab6ecc2873fdf2250e69478270cc6cf07a7b63d0c87f5aa528517). Its ratio \(R\) lives in \(E=F_*\cdot\mathbb Q(\sqrt{-n})\), \(F_*=\mathbb Q(\sqrt5,\sqrt6)\), and is inverted by complex conjugation. This note specifies the **oriented** good-prime exponents from a finite marked embedding count. It does not construct all the marked supersingular orders, evaluate a moving exponent, or prove an efficient global search.

## 1. Exact fixed weighted support, and the dual 241 step

The divisor of \(\mathcal U\) away from cusps is a finite signed list of fixed ordered CM flags \(Q\), with their multiplicities. Form the list from the known lifted real calibration packets, their four rational Atkin operations, and either \(T_5+2\Delta\) or \(T_7\) as specified by the corresponding kernel. For the diagonal, use multiplicity two; keep each actual cyclic-neighbor multiplicity. Denote the resulting list coefficients by \(w_Q\in\mathbb Z\). Its one underlying imaginary field is \(K_*=\mathbb Q(\sqrt{-5})\), even when the local CM conductor changes. No element in this fixed support is a moving target class.

Let \(p\nmid 2\cdot3\cdot5\cdot7\cdot241\,n\) be a rational prime. Fix a prime \(\mathfrak P\) above it in \(E\), and one compatible extension to the fixed support fields, the moving ring class field and \(\mu_{241}\). All relevant CM orders are maximal at this \(p\); Good reduction on the fine flag charts is used. The case of interest has \(p\) inert in both \(K=\mathbb Q(\sqrt D)\) and \(K_*\). If either is split, no fixed horizontal section can meet a moving flag section: the corresponding curve has ordinary reduction, and an ordinary elliptic endomorphism algebra cannot contain the two distinct quadratic fields. At a good prime a vertical constant of the rational function contributes equally at every index, hence cancels in the nontrivial genus-weighted ratio. No cusp is met by the CM flags since their source \(j\) is integral.

For each fixed \(Q\) include its **finite** family of all cyclic 241-neighbors \(Q'\), with the literal induced \(48\)-flag and the dual 241-kernel \(K^\vee\subset A_{Q'}[241]\). These neighbors are still fixed CM calibration data over \(K_*\). The evaluation in the moving family is at a conductor-241 vertical lift of a maximal-order source \(P\). There is a unique ascending 241-kernel from that lift back to its maximal-order neighbor. Over a common residual collision of the vertical lift with \(Q\), this same kernel lifts uniquely on the fixed \(Q\) side: 241 is prime to \(p\) and the level structures are finite étale. Both projections from the fine \(48\cdot241\)-moduli are étale along the noncuspidal points in question (with auxiliary prime-to-\(p\) fine marking if needed). Thus its intersection length equals that of the maximal source \(P\) with the particular fixed \(241\)-neighbor \(Q'\). Conversely an actual maximal CM embedding at \(Q'\) for which \(K^\vee\) is **not** an eigenline of the moving CM order yields precisely one vertical lift; an eigenline is horizontal and is discarded. This is a one-to-one dual-kernel indexing, not a sum over all unlabelled target \(j\)'s.

## 2. Actual prime orientation and local length

Work on the reduction \(A\) of that fixed flagged neighbor \(Q'\) at the named extension of \(\mathfrak P\), with actual full \((C_{16},C_3)\), dual line \(K^\vee\), and actual CM endomorphisms. A moving candidate is an optimal embedding of the maximal order of discriminant \(D\) into \(\operatorname{End}(A)\) with:

1. the named inert Lie embedding of \(K\) (fix a compatible square root of \(D\));
2. the actual line eigenvalues of \(\alpha=(1+\sqrt D)/2\) at both cyclic level flags, on the chosen norm-48 ideal orientation;
3. a non-eigenline \(K^\vee\) at 241.

The inert normalized CM reduction correspondence identifies the first two marked conditions with the actual indexed maximal CM reduction fibre. Here the modulus is prime to the residual characteristic, and the named Lie orientation is not summed over. One way to see the marking is to use the unramified canonical CM lift of an optimal embedding at \(p\); the prime-to-\(p\) cyclic subgroup lifts uniquely, and its split local eigenvalue fixes the full cyclic subgroup at each level prime. This is the same normalized inert correspondence as in the original receiver ([Cornut–Jetchev, §4](https://arxiv.org/pdf/1012.0725v1)). No extra weight from a geometric automorphism is lost: in characteristic \(p>3\) all automorphisms of an elliptic curve preserving this cyclic 16-subgroup are \(\{\pm1\}\). A nontrivial order-three automorphism at \(j=0\) cannot preserve its order-two line, and an automorphism \(i\) at \(j=1728\) cannot act on a cyclic 4-subgroup by a root of \(x^2+1\bmod4\). The surviving \(-1\) is ineffective on the moduli parameter and on the embedding conjugation. These assertions may be made on a fine prime-to-\(p\) cover and descended.

For the fixed \(Q'\) let \(f_*\) be the conductor of its **full 48-flag order** (the least common multiple of the two endpoint conductors over \(K_*\)). The element \(\beta=f_*\sqrt{-5}\) preserves the flag, even if the larger source-curve order has additional endomorphisms. Fix the chosen CM sign of this square root at the place in use. Put
\[
 h_0=\operatorname{Trd}(\alpha\beta)\in\mathbb Z,\qquad
                 H=5f_*^2m-h_0^2 .
\]
The two fields are distinct, so the corresponding pure trace-zero elements are linearly independent in the positive definite norm space and \(H>0\). More explicitly write \(V=2\alpha-1=x\sqrt{-5}+yJ\) in the quaternion decomposition
\[
 B_{p,\infty}=K_*\oplus K_*J,\qquad Jz=\bar z J,\quad J^2=-p u ,
\]
where \(u\) is a unit at \(p\). Locally the maximal order is \(O_{K_*,p}\oplus O_{K_*,p}J\); \(x\in\mathbb Z_p\) and \(y\in O_{K_*,p}\). Since \(h_0=-5f_*x\) and \(m=5x^2+pu\,N(y)\),
\[
 H=5 f_*^2 pu\,N(y),\qquad
        v_p(H)=1+2v_p(y).
\]
Here maximality of either order at \(p\) and \(p\nmid f_*\) are essential.

The exact length of the good-prime intersection in this marked entry is
\[
                              \ell=\frac{v_p(H)+1}{2}.
\]
Indeed the nested endomorphism ring of the fixed source canonical lift modulo \(p^j\) is \(O_{\rm source}+p^{j-1}\operatorname{End}(A)\) for the unramified inert CM type ([Lauter–Viray, §6.4, (6.6)](https://arxiv.org/pdf/1206.6942)). Its local quadratic part is the full \(O_{K_*,p}\), irrespective of the fixed prime-to-\(p\) calibration conductor. Thus \(\alpha\) lifts to depth \(j\) exactly if \(v_p(y)\ge j-1\). With the prescribed Lie root this is the matching canonical deformation: finite étale unramified endomorphism type has a unique Hensel lift of the Lie root, and the canonical unramified Serre–Tate CM lift is characterized by lifting that local action. This is the individual lift/isomorphism step in [Lauter–Viray, §4](https://arxiv.org/pdf/1206.6942), before their later summation over both signs and all CM indices. Full cyclic flags and the lifted dual line are finite étale and add no lifting condition once their mod-\(p\) markings agree. Hence the depth is the intersection multiplicity of literal sections, not an absolute \(j\)-difference factor with an untracked automorphism.

There are two cheap **orientation** constraints, independent of the multiplicity:
- If \(\lambda,\nu\) are the respective scalar actions of \(\alpha,\beta\) on the common cyclic 48-line, then simultaneous upper triangular form gives
\[
                   h_0\equiv \nu(2\lambda-1)\pmod{48}.
\]
One uses the exact line at 16 and at 3. Reduced traces of the upper triangular matrices have diagonals \((\lambda,1-\lambda)\) and \((\nu,-\nu)\); no semisimplicity of the fixed second matrix is assumed.
- The derivative map on the supersingular local quaternion order induces its residue quotient \(O_{B_p}/\mathfrak m_{B_p}=\mathbf F_{p^2}\). Its reduced trace descends to the field trace. Therefore
\[
                     h_0\equiv \sqrt D\,f_*\sqrt{-5}\pmod p
\]
with the **named** Lie roots; both square roots are trace zero. For each \(s_0\in\{1,5,6,30\}\) such that \(p\) splits in \(M_{s_0}=\mathbb Q(\sqrt{-s_0n})\), the oriented prime of this binary projection has the root
\[
       \sqrt{-s_0 n}\ \equiv\
       (h_0/f_*)\,\frac{\sqrt{241s_0}}{\sqrt{-5}}\pmod p .
\]
The ratio of roots is in \(\mathbf F_p\), since \(D,-5,241s_0\) are all nonsquares for these entries. The signs use the compatible fixed radical (coefficient-field) place, not an independently selected square root per entry. This provides actual oriented labels when projecting from \(E\); it does not replace the counting of actual embeddings.

## 3. The signed good-prime ideal sum

On \(A[241]\) take a symplectic frame for one fixed primitive Weil root \(\zeta\) with quadratic Gauss sum equal to the named \(\sqrt{241}\). For any nonzero \(z\in K^\vee\), the primitive genus weight is
\[
                         \left(\frac{\det(z,Vz)}{241}\right).
\]
This is nonzero exactly for a vertical line and is unchanged under a line rescaling or symplectic-frame change. Its **absolute sign** can be normalized on the principal analytic lattice: with basis \(1,\tau=(1+\sqrt D)/2\), the line generated by \(1/241\) gives the principal \((1/241)\mathcal O_{241}\) quotient and has determinant \(2\), a square modulo 241. The same factorization of the Gauss weight persists at any good prime. Along a base CM ideal isogeny of degree \(d\) prime to 241 the determinant scales by \(d\) in the common Weil frames, giving exactly its old quadratic factor. In a relative fibre the change \(z\mapsto w z\) scales by \(N(w)\), the local genus norm on the split or inert quadratic étale module. Thus there is not a separate unknown sign at each prime or each calibration point. Choosing a different extension of the given oriented prime changes all labels coherently; the weighted sum of the fully lifted packets is invariant, as \(R\) belongs to \(E\).

Consequently, at any such inert good place the actual exponent \(v_{\mathfrak P}(R)\) is the sum, over the full fixed signed support, its finite fixed 241-neighbors, and the literal marked maximal embeddings satisfying 1–3, of
\[
                       w_Q\,\left(\frac{\det(z,Vz)}{241}\right)
                                \frac{v_p(5f_*^2m-h_0^2)+1}{2}.
\]
For split ordinary places the good-prime exponent is zero. For a binary norm to \(M_{s_0}\), aggregate these exact exponents over the primes above the specified binary prime, multiplying by their residue degrees. No absolute-valuation formula for a total CM product is substituted. Any nonhorizontal vertical divisor on a smooth irreducible good fibre is constant in the original indexed sums and cancels.

The support can be sought among rational primes of the integers \(5f_*^2m-h_0^2\), with the exact level congruence and \(0<5f_*^2m-h_0^2\). This is not a polynomial-in-bit algorithm: the displayed interval still has order \(\sqrt m\) possibilities before any additional compression. Nor does this theorem here implement the calibrated maximal quaternion rings and signed Tate data. No evaluated exponent, noncube, or rank follows.

## Appendix: the small quaternion presentation

For an odd \(p\ne5\) inert in \(K_*\), one may take \(u=1\) when \(p\equiv3\bmod4\), and \(u=2\) when \(p\equiv1\bmod4\). Indeed \((-5,-pu)\) is nonsplit at \(p,\infty\). With \(u=1\), the extra local Hilbert signs at \(2,5\) are both positive in the first case and both negative in the second (use the inert norm parity and \((-5/p)=-1\)). Multiplying the second entry by 2 flips both extra signs and does not change the signs at \(p,\infty\); other primes are units of odd residue characteristic. Thus this is the correct rational quaternion algebra. It determines neither a concrete maximal **order** nor its calibrated flag bases.
