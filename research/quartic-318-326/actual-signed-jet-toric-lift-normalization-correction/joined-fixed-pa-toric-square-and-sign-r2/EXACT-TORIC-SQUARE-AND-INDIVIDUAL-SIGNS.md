# The normalized product is a literal same-place square; both central signs are positive

Supplies two refinements of [the matching-vector lift](../joined-fixed-pa-actual-toric-lift-r2/THE-ACTUAL-SIGNED-JET-HAS-A-MATCHING-WALDSPURGER-LIFT.md). Use its exact \(p,N,\Delta,\psi,b_\Delta,\Phi\) and level-\(Np^2\) transfer \(g\). The statement does not prove either central value nonzero or a \(p\)-unit on the retained ray.

## 1. The dual vector is the same torus translate

The central character is trivial, so the \(\mathrm{GL}_2\) transfer is self-dual (its contragredient is its twist by the inverse central character); Jacquet–Langlands and multiplicity one identify the contragredient definite representation with the same space of functions \(\pi\). Use the bilinear Petersson pairing of [Cai–Shu–Tian (2.1)](https://arxiv.org/pdf/1408.1733), not complex conjugation of algebraic coefficients.

Let \(t_0\) have all local components 1 except for a ramified uniformizer of \(K_p\). Let \(u=b_\Delta^{-1}\iota(t_0)b_\Delta\) and \(R(u)\Phi(x)=\Phi(xu)\), and choose \(\Phi^\vee=R(u)\Phi\). This is an integral function at the **same** place (argument translation preserves the value set). Its \(p\)-axis is \(\widetilde\tau^{-1}\) since the ramified uniformizer normalizes maximal units and acts by residue Frobenius. The other local vectors are unchanged. The local bilinear dual pairing between the two opposite axes at \(p\) is nonzero: invariance pairs each nonzero eigenline only with its inverse, and the pairing is nondegenerate. At a tame or spherical one-dimensional fixed line it is likewise nonzero (average over the compact subgroup in characteristic zero); at infinity it is the pairing of trivial lines. Thus the global pairing on these pure tensors is nonzero. The normalized local matrix coefficient on the other coset still vanishes: it pairs two vectors in the \(\widetilde\tau^{-1}\) axis, and \(\widetilde\tau^2\ne1\).

For \(S=\sum_{[a]}\psi(a)\Phi(\iota(a)b_\Delta)\), the dual class sum is
\[
 \sum_{[a]}\psi(a)^{-1}\Phi(\iota(a)b_\Delta u)
 =\sum_{[a]}\psi(a)\Phi(\iota(a t_0)b_\Delta)
 =\psi(t_0)^{-1}S=S.
\]
In the last equality \(\psi(t_0)=(h'/p)=+1\). This is a permutation of the same full class group; neither the marking nor the frame orientation is changed on the resulting sum. Consequently the right-hand side in the CST equality of the preceding note, **with this specific dual**, is exactly \(S^2\). Its \(p\)-unit property is equivalent, not just sufficient, to the original \(\mathcal J_p\ne0\). There is no conjugate residue-place assumption. The product keeps the actual Petersson normalization; that factor is not asserted to be a \(p\)-unit by multiplicity one.

## 2. Local epsilon at the new squared prime

Write \(F=\mathbb Q_p\), and \(L/F\) for its unramified quadratic extension. The depth-zero parameter of \(g\) is \(\operatorname{Ind}_{W_L}^{W_F}\vartheta\), with residue character \(\widetilde\tau^{\pm1}\), up to the choice of unramified-quadratic reciprocity orientation. Its central determinant is trivial, so \(\vartheta(p)=-1\) (restriction to \(F^\times\) is the unramified quadratic character, cancelling the induction determinant). The lambda factor for the unramified quadratic extension at the usual conductor-zero additive character is 1. Apply the conductor-one Gauss formula of [Tate, Number theoretic background, §§3–4](https://ncatlab.org/nlab/files/TateNumberTheory.pdf), or the induced-character calculation in [Pacetti, §3](https://arxiv.org/pdf/1010.3781). The following computes the finite Gauss sign exactly, with no numerical complex sums.

Put \(\xi=\widetilde\tau^{\pm1}\), and choose \(z_0\ne0\) of trace zero in \(\mathbb F_{p^2}\). Then \(\xi(z_0)=-1\), since \(z_0^p=-z_0\). More generally for any nontrivial \(\xi\) trivial on \(\mathbb F_p^\times\), the sum of \(\xi^{-1}\) over the nonzero trace-zero slice is \((p-1)\xi(z_0)^{-1}\); all nonzero trace slices have the same sum by scalar multiplication, equal to \(-\xi(z_0)^{-1}\) by total character orthogonality. Pairing with a primitive additive character of the trace gives \(G(\xi^{-1})=p\,\xi(z_0)^{-1}\) (unchanged if the additive character has the opposite sign). Thus \(w_p(g)=\vartheta(p)G/p=+1\). This is a local epsilon calculation; the ramified torus projection in the previous note does not determine this sign by itself.

For the actual ramified quadratic twist by \(d'=rD\) at \(p\), \(\vartheta(p)\) is unchanged because the local norm of \(p\) from \(L\) is \(p^2\). On residues the additional character is the quadratic character of the norm. Its value on \(z_0\) is \(-1\): \(N(z_0)=-z_0^2\), \(z_0^2\) is nonsquare in \(\mathbb F_p\), and \(p\equiv1\bmod4\). The twisted residue character remains regular (its square is unchanged). Thus \(w_p(g^{d'})=-1\). For the fixed \(h'\) twist \(w_p\) is unchanged since the conductor exponent is 2 and the twist is unramified.

## 3. Individual global signs and exact bounded comparisons

At tame level the unchanged signs multiply to \(-1\), and weight two gives archimedean sign \(-1\), so \(w(g)=+1\). The exact fixed twist signs at the seven tame primes are \((+,+,-,-,+,-,+)\), and at \(p\) the fixed character is \(+\). Since \(\chi_{h'}(-1)=-1\), the twist of coprime conductor gives \(w(g^{h'})=+1\).

For \(d'\), at \(2,3,5,7\) the quadratic twist is unramified with character \(\chi_{h'}(\ell)\), giving local signs \((-,+,-,+)\). At \(11,37,2399\) ramified quadratic twist of unramified Steinberg gives \((-1/\ell)\), namely \((-,+,-)\). At the other three actual movers (different from \(p\)) ramified twist of good reduction gives \((-1/q)=+1\), because the retained primes are \(1\bmod8\). All remaining finite signs away from \(p\) are \(+\). Combining with \(w_p=-\) and the archimedean \(-\) gives \(w(g^{d'})=+1\) separately. This also agrees with the product sign by CST.

For independent arithmetic replay:

    python3 -B check_toric_square_and_sign.py | cmp - EXACT-LOCAL-SIGNS-AND-COMPARISON.json

The numeric two-factor comparison uses the exact old state \(D=19871020087852834114214638801\). Its \(\Delta=-42820048291022035216231785026974318151\) has the same seven tame quadratic symbols \((+,+,+,+,0,0,0)\), while \(p\) is simply ramified. In a local canonical formal frame with \(p^2\)-Frobenius \([-p]\), the phase \(c_0\) satisfies
\[
  c_0^{p+1}=-\Delta/p\bmod p=389840.
\]
Indeed \(v=\sqrt\Delta\) has leading coordinate term \(c_0z^p\), and \(v^2=[\Delta]\) has leading coefficient \(-(\Delta/p)\) in degree \(p^2\) in that frame. One norm representative in \(\mathbb F_p[\sqrt3]\) is \(206541+7\sqrt3\). This is **only** a norm representative, not the actual signed phase or a computed period. The numeric \(D\) fails the old denominator saturation and the actual original three-pole compatibility, and is not production.

There is also a much smaller **fixed-factor diagnostic**: keep the same \(g,p,h'\) but allow a different illustrative positive fundamental discriminant \(d=p m\). Require \(m\equiv1\bmod8\), squarefree and prime to \(p h'\), so the level-2 split condition holds. At every odd tame prime permit split, or ramified with \((h'/\ell)=w_\ell\). The least two such \(m\)'s are \(113,177\), with \(|h'd|=103677075911,162396835719\). The former splits all tame level, the latter ramifies only at 3 among them. The local tests therefore apply to this very same lift and fixed \(h'\) factor, subject to evaluating the signed finite class sum with an oriented optimal embedding. A **computed nonzero** such sum would prove that a fixed central factor in every production product does not vanish; it would not prove any varying production factor, and no such sum has yet been computed. These smaller inputs do not share the original ray, selected marks, or proof implication.
