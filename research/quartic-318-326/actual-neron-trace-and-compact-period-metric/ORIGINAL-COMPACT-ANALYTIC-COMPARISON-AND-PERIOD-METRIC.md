# Glue the same ordinary chart to the same compact period metric

Fix the actual signed primitive polynomial \(p\) and entire original
rational normalization \(X\to\mathbf P^1_J\), at the chosen level
\(M\ge5\). Let \(X_\sigma\) be its actual complexification and let
\(X_{\Gamma_1}^{\rm an}\) be the compact analytic
\(\Gamma_1(M)\)-quotient, with its usual elliptic and cusp charts.
Write
\[
        V=\mathbf P^1(\mathbf C)\setminus\{0,1728,\infty\}.
\]
No independent compact isomorphism or comparison of canonical bases
is an input to this argument.

## The compactification comparison follows from the same ordinary J

On \(V\), the original affine model has the whole monogenic complex
root locus, not a chosen factor. Its vertical derivative is a unit by
the original simple-chart theorem. The signed marked-period
coordinates therefore give a biholomorphism over \(V\) from the
actual ordinary quotient to this root locus: the fibers are exactly
the \(\Gamma_1(M)\) orbits, the map reaches every root, and in every
simple-root graph the coordinate \(J\) identifies the native local
charts. The source is holomorphic in the same \(J\)-coordinate by
the actual local inverse of the modular \(J\) function at every
ordinary period. None of this uses an independent compact model.

The original normalization is a normal projective curve, hence
regular in dimension one and smooth over the characteristic-zero
coefficient field. Its complexification is the same geometrically
connected curve; the whole ordinary complex field, rather than a
selected factor, verifies the connectedness here. The smoothness
criterion is [Stacks, Section 33.12](https://stacks.math.columbia.edu/tag/038S).
Both complex compact curves consequently have finite holomorphic
maps to the same \(J\)-sphere. On each side choose a coordinate \(t\)
in a small target disk around a missing value: \(J-c\) at \(c=0,1728\)
and \(1/J\) at infinity.

At each point over the disk center, choose a source coordinate
\(z\) with \(t=z^e\), for a positive integer \(e\). To see the exact
form, the holomorphic germ first has the form \(z^e u(z)\) with
\(u(0)\ne0\); on a smaller simply connected disk absorb a
holomorphic \(e\)-th root of \(u\) into the coordinate. Disjoint
small source disks about the finitely many points over the center
can be chosen simultaneously. Properness permits shrinking the
target disk until its full preimage is in those disks, and shrinking
again makes each component a disk mapping by the indicated power.
The previously identified ordinary comparison maps the connected
components of the deleted preimage disks bijectively, preserving
the covering degree \(e\) of each component. Thus it does not pair
a cusp with a branch of different width or pick an unidentified
limit sheet. On a matched pair with coordinates \(z,w\), its
over-\(J\) relation reads \(w(z)^e=z^e\) on the connected
punctured disk. The quotient \(w(z)/z\) is consequently one constant
root of unity there. The map and its inverse extend across zero by
that same linear formula. The local extensions glue to a unique
biholomorphism of the two actual compactifications over the literal
\(J\). This does not require a general GAGA comparison of modular
curves; it uses analytification of the original finite complex
curve and the explicit normal disk construction.

## No new basis or metric factor

Let \(\underline\omega=(\omega_i)\) be the original algebraic basis,
and write on the literal open \(a_i\,dJ=\omega_i\).
The corresponding native cusp forms satisfy exactly
\[
               f_i(\tau)=a_i(J(\tau),x(\tau))\,J'(\tau).
\]
Consequently the compact holomorphic forms are the same forms:
they agree on the ordinary open and extension through the finitely
many omitted fibers is unique. In a true quotient chart the
conjugate-first energy density is
\(\overline{f_i} f_j\,dx\,dy\).
The hyperbolic measure contributes \(y^{-2}\) and the weight-two
Petersson product contributes \(y^2\), without a remaining factor.
The finite omitted set has zero area in any smooth local complex
chart, so the same quotient integrals give the compact Gram
\[
       G_{ij}=\int\overline{f_i}f_j\,dx\,dy .
\]
This uses the actual basis and actual embedding \(\sigma\); it
does not replace the forms by an independent orthonormal basis in
the arithmetic determinant.

Choose one ordered symplectic homology basis on this compact
curve and write the actual period matrices \(P,Q\) of the given
forms. The bilinear relation for closed one-forms \(u,v\) reads
\(\int u\wedge v=\sum_k
(\int_{a_k}u\int_{b_k}v-\int_{b_k}u\int_{a_k}v)\);
it follows by cutting along the cycles, taking a primitive of \(u\)
on the resulting polygon and applying Stokes to its boundary.
For the holomorphic forms the first relation gives \(PQ^t=QP^t\);
for a form and a conjugate the second gives
\[
             G^t=\frac{i}{2}(P\bar Q^t-Q\bar P^t).
\]
Positive definiteness implies \(P\) is invertible: if a linear
combination has every \(a\)-period zero, its self-pairing by the
second formula vanishes. Put \(Q=P\tau\). The first relation then
gives \(\tau^t=\tau\), and the second gives
\(G^t=P\,\Im(\tau)\,\bar P^t\).

The Abel--Jacobi map sends these actual cycles to the generating
period lattice of the complex Jacobian, preserving their invariant
forms. Integrating the invariant top wedge over its fundamental
parallelotope with the unshifted factor \(2^{-g}\) gives the real
covolume
\[
 \left|\det_{\mathbf R}
 \begin{pmatrix}\Re P & \Re Q\\ \Im P & \Im Q\end{pmatrix}\right|
 =\det G.
\]
For the exact matrix identity multiply the real block (complexified)
by \(\begin{pmatrix}1&i\\1&-i\end{pmatrix}\) in block scalars;
subtract the first block row from the second. The same
\((-2i)^g\) factor appears on both sides of the resulting determinant
identity, and cancels. The ordered transpose and \(i/2\) convention
are explicitly checked by the native algebraic
SelectedPeriodBlockDeterminant318 endpoint.

It follows that the unshifted norm of the same wedge is
\(\sqrt{\det G}\). The height convention with
\(\frac{1}{(2\pi)^g}\) in place of \(2^{-g}\) in the squared norm
multiplies it by \(\pi^{-g/2}\), so the negative log acquires
exactly \(+\frac g2\log\pi\), with no level, width, power of 2, or
embedding factor. Multiplying the wedge by the determinant of the
same inverse \(J=1\) minor multiplies both norms identically.
This is the geometric comparison for the exact native Gram height
expression; it is not a Lean construction of analytification, the
Abel--Jacobi period torus, or integration on singular homology.
