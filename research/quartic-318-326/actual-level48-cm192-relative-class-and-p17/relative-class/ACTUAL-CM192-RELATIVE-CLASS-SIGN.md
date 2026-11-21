# The next marked sign from a relative ideal-class relation

For either genuine balanced detector twist, the coherent second-saturation sign of the level-48 trace can be determined by one relative ideal-class relation over the fixed real quartic \(\mathbf Q(\sqrt3,\sqrt{17})\), instead of computing a norm-one algebraic generator. Every prime above 17 has **even** exponent in the relevant fractional ideal, regardless of the remaining squarefree support. At present neither the full ideal nor its desired class relation is computed.

## 1. One smaller CM field and the exact residue sign

Use the actual \(T=(3+2\sqrt3,2(3+2\sqrt3))\) halving \(T_3\), its cyclic-four quotient \(\lambda:E_0\to E'\), the normalized Miller root \(R_4\), the full CM orbit, and its \(U_4=C_4/(12^{h/8}M)\) from the cyclic-four paper. The raw trace has an exact rational quarter \(B_D\) after twisting, possibly zero. If \(B\in E_0(K)\) is its image, choose the arbitrary lifts for \(C_4\) so that their sum is **exactly** \(\lambda(B)\): change one lift by the needed element of the dual kernel \(\mu\). This changes the existing \(U_4\) only by a global fourth root of unity, so its fractional ideal is unaffected.

Now the sum of lifts is in \(E'(K(\sqrt3))\), not just in \(E'(K(i,\sqrt3))\). For an automorphism over \(K(\sqrt3)\), the changed kernel elements in the index permutation sum to zero. Apply the character of the rational function \(R_4\) to that sum: their factors multiply to one, even if the kernel elements are not individually rational in that field. Hence \(C_4\in K(\sqrt3)\). Write
\[
 F=\mathbf Q(\sqrt3,\sqrt{17}),\qquad L=FK,\qquad U\in L^\times
\]
for the re-normalized product. Here \(F\) is totally real, \(L/F\) is CM quadratic with conjugation fixing \(F\) and negating \(\sqrt D\), and \(U\bar U=1\).

At the comparison primes \(q_0,p_\beta\), the prior proof gives reduction \(\xi(\lambda(\widetilde B))\in\{\pm1\}\) with no common kernel multiplier, because the sum has been chosen to equal \(\lambda(B)\). Their difference of sign is exactly the mark coefficient of a rational quarter after quotienting by its rational 2-torsion ambiguity. Changing the reference rational quarter adds a single rational torsion element, so only the common sign can change. All primes above a given comparison prime see the same sign: the character on the reduced \(\lambda(E_0[2])\) depends only on whether the reduction of \(B\) is in \(\{O,T_3\}\), not the view of the other generators. Opposite signs imply raw trace nontorsion and the actual mark; equal signs only mean the raw trace is an eighth multiple.

The only roots of unity of \(L\) are \(\pm1\). One way to see this is that an abelian extension of exponent two containing a primitive root of unity of order \(m\) has \(m\mid24\) (by the units of \(\mathbf Z/m\)). Any nonreal quadratic subfield of \(L\) has a squareclass \(D,3D,17D,51D\) and hence contains the genuine prime factors of \(\beta\) in its squarefree part. In particular neither \(i\) nor a primitive cube root of unity is present. Thus a unit of norm one, whose absolute value at each complex embedding is one, is \(+1\) or \(-1\).

## 2. Exact class-relation criterion

Let \(\mathfrak U=(U)\), the fractional ideal in \(L\). Since \(\overline{\mathfrak U}=\mathfrak U^{-1}\), choose any fractional ideal \(\mathfrak b\) with
\[
 \mathfrak U=\mathfrak b/\overline{\mathfrak b},\qquad
 \operatorname{ord}_{\mathfrak P}(\mathfrak b)=0
       \text{ at every conjugation-fixed prime}.
\]
For example put the prescribed exponent on one of each conjugate split pair of primes, and zero on the other. The finite ramified primes of \(L/F\) are exactly those above \(p\mid n,\ p\ne17\). At 2 and 3 \(K\) splits locally. At 17, \(F\) already contains \(\sqrt{17}\) and the unramified quadratic \(\mathbf Q_{17}(\sqrt3)\); \(D/17\) is a rational unit and therefore a square in that unramified residue field, and a square locally. At all other \(p\mid n\), \(F\) is unramified and \(D\) has odd valuation, giving the relative ramification and uniformizer \(\sqrt D\). No other finite primes ramify in \(L/F\).

Supply any vector \((e_{\mathfrak P})\in\mathbf F_2^{\{\text{finite ramified }\mathfrak P\}}\) such that
\[
 [\mathfrak b\textstyle\prod_{\mathfrak P\ \mathrm{ram}}\mathfrak P^{e_{\mathfrak P}}]
 \in\mathrm{im}\bigl(\mathrm{Cl}(F)\longrightarrow\mathrm{Cl}(L)\bigr).\tag{1}
\]
Such a vector exists. By Hilbert 90 \(U=\alpha/\bar\alpha\). The quotient \((\alpha)/\mathfrak b\) is conjugation-invariant, and every such fractional ideal is an extended ideal from \(F\) times powers of relative ramified primes, with exponents on the latter reduced modulo two. Conversely, any relation (1) gives a generator \(\alpha\) after multiplying by a suitable extended ideal, and then \(U/(\alpha/\bar\alpha)\) is a norm-one global unit, hence \(\pm1\). No generator needs to be computed to check that sign difference.

Indeed at a relative ramified prime of odd residue characteristic, conjugation fixes the residue field and sends \(\sqrt D\) to \(-\sqrt D\). It follows that
\[
 \alpha/\bar\alpha\bmod\mathfrak P=(-1)^{\operatorname{ord}_{\mathfrak P}(\alpha)}
                                 =(-1)^{e_{\mathfrak P}} .
\]
Extended ideals from \(F\) have even order here. Thus the desired comparison is exactly
\[
 \boxed{e_{\mathfrak P(q_0)}+e_{\mathfrak P(p_\beta)}\in\mathbf F_2.}\tag{2}
\]
Any two certified relations give the same comparison, since their resulting norm-one principal generators differ in ratio only by \(\pm1\). This reduction needs the actual oriented intersection ideal, not a choice of a sign for an isolated local square root.

There is a further sufficient shortcut. If one can explicitly exhibit a quadratic Artin character of \(L\), pulled back from a quadratic extension of \(F\), unramified over \(L\), whose evaluations on these relative ramified primes give the linear functional in (2), its single value on \(\mathfrak b\) determines the sign. It kills the extended ideal classes from \(F\): on a good split prime the two degree-one evaluations multiply to one, on an inert prime residue degree two makes the character square, and on a ramified prime extension of ideals doubles the order. Representatives coprime to the auxiliary ramification suffice. On a conjugate split prime pair of \(L/F\) the two character values agree, so its evaluation on \(\mathfrak b\) uses the signed intersection exponent only modulo two; the two genus halves then enter with the same sign modulo two. Existence of such a detecting character has **not** been shown here. Characters merely lifted from \(K\) do not see the individual \(q_0\)-prime: \(q_0\equiv7\bmod24\) gives \((3/q_0)=-1\), so the residue degree over the \(K\)-prime is two.

## 3. The 17-component is even for both arms

At a prime above 17, use the simple intersection and class-index involution of the preceding paper. Every collision contributes one in the absolute ramified uniformizer; the signed count from every two-element orbit is even because the involution preserves the genus halves. Fixed collision classes are exactly the \(k=0\) ones. If such a class exists, \(B_{17,\infty}=(-3,-n)\), so by the local Hilbert-symbol argument every rational prime dividing \(n/17\) splits in \(K_0=\mathbf Q(\sqrt{-3})\). In particular if a companion introduces any inert prime, there are no fixed collision indices and the parity is already zero.

Otherwise, on either Fricke-fixed flag at 17, use the transported Frobenius \(\pi\) from \(j=0\) with \(\pi^2=-17\). An anti-commuting \(u\) is \(\gamma\pi\) with \(\gamma\in K_0\), \(N\gamma=n/17\). In fact \(\gamma\) is integral. At primes other than 2 and 17 the transport has degree a 2-power and \(\pi\) is invertible in the localized endomorphism ring, so \(\gamma\) is integral. At 2 and 17 the norm of \(\gamma\) is a unit in the inert quadratic algebra, so \(\gamma\) is integral there too. Since \(n/17\) is squarefree, for each rational split factor exactly one of its two Eisenstein primes divides \(\gamma\).

Choose any one genuine original prime \(r\mid\beta/17\), hence \(r\equiv1\bmod24\). Let \(\varpi_r\) have norm \(r\); use an Eisenstein cube root of unity to arrange \(\varpi_r\equiv1\bmod2O_0\). Writing \(\varpi_r=a+b\omega\), \(a\) is odd, \(b\) is even, and \(a^2+ab+b^2\equiv1\bmod8\) then forces \(8\mid b\): write \(b=2c\), so \(2c(a+2c)\equiv0\bmod8\) and \(a+2c\) is odd. In particular \(\varpi_r=A+Bv\in O_8\) for \(v=4\sqrt{-3}\), \(A=a+b/2,\ B=b/8\). Its ratio to the conjugate has the precise form
\[
 \frac{\varpi_r}{\bar\varpi_r}
 =\left(1-\frac{96B^2}{r}\right)+\frac{2AB}{r}v.
\]
At 2 the scalar coefficient is \(1\bmod32\) and the \(v\)-coefficient is even, also for its inverse. At 3 its residue modulo the unique prime of \(K_0\) is one, since conjugation is trivial there.

Swap the single chosen \(r\)-prime factor in \(\gamma\), using the displayed ratio or its inverse according to the factor present. This changes the normalized embedding to a different one, keeps the same norm, and preserves the exact flag and its **same** orientation. To verify the last points without an appeal to a group-theoretic distribution statement, use the lattice \(O_{8,2}=\mathbf Z_2[v]\) and the scalar \(\eta=\eta_0\gamma=A_\eta+B_\eta v\) of the semilinear \(u\) on \(K_{0,2}\). The condition \((1+\eta\,\mathrm{conj})/2\) is integral precisely when \(A_\eta\) is odd and \(B_\eta\) even, by its value on \(1,v\). When it is integral, \(C_{16}=\ker v\) identifies with \(O_{8,2}/vO_{8,2}=\mathbf Z/16\) via multiplication by \(v\). Since \(v\omega_D=(1-\omega_D)v\), the eigenvalue of \(\omega_D\) on cyclic \(C_{16}\) is \((1-A_\eta)/2\bmod16\). The swap preserves this exactly: multiplication by the ratio leaves \(A_\eta\bmod32\) unchanged and its \(v\)-coefficient even. At 3 the same identification with the quotient by \(v\) shows the eigenvalue is unchanged because the ratio has residue one there. These eigenvalues specify the two level primes, since \(D\) is a square unit at 2 and 3 and the two roots for \(\omega_D\) differ by \(\sqrt D\), a unit.

Hence the swap acts involutively on the fixed collision classes for each of the two fixed flags at the chosen place, using the uniqueness of normalized Deuring lifts. It has no fixed class: the \(r\)-prime in \((\gamma)\) changes, and the flagged automorphisms are only \(\pm1\), which do not conjugate one embedding into a different one. It follows that the total number of fixed collision classes is even. With the paired nonfixed indices this proves
\[
 \boxed{\operatorname{ord}_{\mathfrak P}(U)\equiv0\bmod2
       \quad\text{for every }\mathfrak P\mid17.}
\]
The absolute ramification index there is two (the ramified quadratic \(K\) becomes split over \(F\) locally), so each simple intersection contributes exactly one to this order. The proof works on either balanced twist, not just the retuned arm used to construct a collision, and is consistent with a nonzero **even** signed order.

For the particular first-arm selector with a helper \(r\equiv1\bmod24\) and \((17/r)=-1\), the \(k=0\) terms actually cancel **as signed integers**. Conjugating the normalized embedding by the other Eisenstein \(r\)-endomorphism realizes the swap, since \(\pi\) conjugates \(K_0\). This endomorphism on the fixed flagged curve commutes with \(v\) and has degree \(r\). Its kernel is stable under the original \(O_K\)-action by the intertwining, so the lifted isogeny is the characteristic-zero isogeny of the unique ramified \(r\)-ideal of \(K\), retaining both level primes. That ideal has \(\chi_{17}\) value \((17/r)=-1\), so the paired collision contributions have opposite sign and equal multiplicity. This does not cancel general \(k\ne0\) contributions.

### Exact source pins

- *The next detector saturation sign is an oriented CM intersection ideal*, paper **c83ce5b2c7d6c95283d67f375f3c306f8ed62ead52c344c78d33ba991724ae7e**, fixes the chosen fibre, actual quarter and signed ideal.
- *A genuine marked CM intersection at 17 after an admissible final prime refinement*, paper **06ba1eb579ce92bfeffeedcab4ef2fa3e239d461dee25828a00334bf94027ea5**, fixes simple multiplicity and the \(k=0\) reduction. Its ring arithmetic controls also apply to the same 2-adic marked lattice.

No actual class relation (1), sign (2), rank, or mark is asserted. The good-place ideal outside these exclusions and its 2,3 components still need to be computed.
