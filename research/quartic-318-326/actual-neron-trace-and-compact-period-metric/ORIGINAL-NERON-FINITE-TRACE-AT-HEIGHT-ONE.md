# The same Néron lattice gives regular finite traces without extending across nodes

## Precise sufficient geometry

Keep the selected entire signed compact generic curve \(X=X_1(M)_L\),
its literal \(J\)-map, the actual \(J=1\) centers \(\beta_i\), and
the same Abel--Jacobi map to \(\operatorname{Jac}(X)\) based at a center.
Write \(F=L(X)\) and \(K=L(J)\). At a finite place \(v\), set
\[
 O=\mathcal O_{L,v},\qquad A=O[J],\qquad
 B=\text{integral closure of }A\text{ in }F.
\]
Use the original normalization \(Y\to\mathbb P^1_O\), with its given
finite flat map. The only additional local geometry needed below is
that the codimension-one points of \(Y\) above the affine chart are
in the \(O\)-smooth locus. A full regular model comparison of entire
dualizing lattices, or extension of the Abel--Jacobi map through nodes,
is unnecessary.

To supply this condition at every place simultaneously, apply
[Javanpeykar, Theorem 4.3.2](https://msp.org/ant/2014/8-1/ant-v8-n1-p04-s.pdf#page=31)
to the actual finite \(J\)-map after the \(J=1\) splitting field.
The theorem gives one further field \(L\) and the finite flat
normalization \(Y\) with semistable minimal regular resolution
\(\rho:Z\to Y\). This remains the unrestricted semistable field \(L\);
it is not the bounded modular comparison field.

Indeed, a prime \(P\) of \(B\) over a height-one prime \(q\) of \(A\)
has height exactly one. It is nonzero, and incomparability for the
integral extension bounds the length of strict prime chains below it
by the length below \(q\). The only point above \(0\) is the generic
point of the same field \(F\). Since \(Y\) is normal, it is regular
at \(P\), and its resolution is an isomorphism there. For a horizontal
\(P\), the corresponding point on \(Z\) is in the characteristic-zero
smooth generic curve. For a vertical \(P\), its counterpart on \(Z\)
has codimension one and is the generic point of a special-fiber
component: a nonzero uniformizer lies in that prime, and no smaller
nonzero prime lies below a height-one prime. The nonsmooth points of
a semistable relative curve are isolated nodes in the special fiber,
not these generic points. Thus \(P\) lies in \(Y^{\rm sm}\), as claimed.
This uses neither a minimality assertion about \(K_Z\) nor negativity
of an exceptional intersection matrix.

## Actual finite trace test, not a branch trace

Let \(H_v=e^*\Omega^1_{\mathscr J/O}\) be the actual invariant Hodge
module for the Néron model of the same Jacobian over \(O\). The generic
Abel--Jacobi map extends to \(Y^{\rm sm}\to\mathscr J\), by the
[Néron mapping property](https://msp.org/ant/2010/4-2/ant-v4-n2-p01-s.pdf#page=24)
on the smooth \(O\)-scheme \(Y^{\rm sm}\), even though \(Y\) itself
need not be regular everywhere. Translation extends each element
\(\lambda\in H_v\) to a regular differential on \(\mathscr J\).
Write its pulled-back generic form as \(a_\lambda\,dJ\).

For a height-one \(q\subset A\), use the **finite semilocal**
\(B_q=B\otimes_A A_q\). Its entire spectrum maps into \(Y^{\rm sm}\):
its points lie over \(0\) or \(q\), and the preceding argument covers
all of them. This does not claim that each individual \(B_P\) is
finite over \(A_q\), nor that the full field trace preserves a
single branch localization. Since \(\operatorname{Spec} B_q\) maps
through \(Y^{\rm sm}\), restricting the actual pulled-back regular
form meets every point of this semilocal model without needing a
section at any removed node.

To use finite duality on finite-type schemes before taking this
localization, let \(Z_{\rm bad}\) be the closed nonsmooth complement
in the affine inverse image. The finite map sends \(Z_{\rm bad}\)
to a closed subset of \(\operatorname{Spec}A\) not containing \(q\).
Choose a principal open \(D(f)\) containing \(q\) in its complement.
Its whole finite inverse image is smooth over \(O\). Apply the
following relative duality on \(D(f)\) and then localize to \(A_q\);
no finite type assertion about \(A_q\) itself is needed.

Finite duality with the base frame \(dJ\) identifies the regular
relative form there with an element of
\[
 \operatorname{Hom}_{A_q}(B_q,A_q)\,dJ .
\]
Here the finite relative dualizing module is the finite Hom
([Stacks, 0FKW](https://stacks.math.columbia.edu/tag/0FKW));
its twist by the base top differential is the relative canonical
module of the composite, by composition for shriek and smooth
relative duality ([Stacks, 0AU3](https://stacks.math.columbia.edu/tag/0AU3)).
On the \(O\)-smooth locus this is the stated top Kähler form.
On the separable generic field the Hom is identified with the
actual trace pairing, with its canonical counit
([Stacks, 0BW0](https://stacks.math.columbia.edu/tag/0BW0)).
The generic coefficient \(a_\lambda\) is therefore the same, and
for every \(b\in B\) we have
\[
                \operatorname{Tr}_{F/K}(a_\lambda b)\in A_q .
\]
Intersecting these base localizations in \(K\) gives
\(\operatorname{Tr}(a_\lambda B)\subset A\). This is the ordinary
scalar intersection for the UFD \(O[J]\), not a Hartogs
extension of a sheaf on the possibly singular model \(Y\).

In particular the actual pullback is the unique element of the
global affine finite Hom with this generic coefficient. The native
boundary **SelectedOriginalAbelPullFromLocalTrace318.ofLocalTrace**
takes precisely these height-one scalar trace tests and produces
the previous AbelPullAt data. The geometric proof of the tests
given here remains a paper construction, not an asserted Lean
implementation of Néron models or Grothendieck duality.

## No other change to the height argument

Use the already proved all-prime clearing \(MJ(J-1728)\) on that
same normalization and the original marked \(J=1\) sections.
The evaluated columns are literally the same
\[
             I_v=(-1727M)\,m C_v \ \in M_g(O),
\]
with the same ordered minor \(m\) and actual \(C_v\) from the Néron
basis. Nothing changes at the wild-level places, in the absolute
normalization of \(\log|\det(mC_v)|_v\), or in the archimedean Gram.
This shortening only replaces the earlier smooth-locus pullback
plus Hartogs route by a direct test on the normal affine model.
