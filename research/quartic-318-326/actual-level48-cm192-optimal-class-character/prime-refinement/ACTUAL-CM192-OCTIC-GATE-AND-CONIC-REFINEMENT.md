# A controllable quartic-residue gate for the first-arm octic character

For the actual first balanced arm, an unramified order-eight class character detecting the marked CM ideal can exist only if a specific product of quartic residues is \(-1\). This product can be prescribed either way by refining the same shared final prime without changing the old Selmer matrices, the literal \(b\), or the companion selector. Moreover one can simultaneously make the rational norm conic from the previous class test admit a solution with numerator coefficient of \(\sqrt D\) equal to one. The residue gate \(-1\) is necessary, not proved sufficient for a detecting character, and the actual signed Heegner ideal remains unknown.

## 1. The only possible genus restriction over the original quadratic field

Use the actual first arm \(n=\beta Hq_0\), \(H=\prod I_j\), with \(u=1,v=\theta\), \(q_0\equiv7\bmod24\), no repair prime, and the established Selmer-eight mark \((\beta,1)\). Use \(D=-n\), \(K=\mathbf Q(\sqrt D)\), \(F=\mathbf Q(\sqrt3,\sqrt{17})\), and \(L=FK\). All primes dividing \(\beta H\) are \(1\bmod4\) and in fact \(1\bmod8\), including 17. The one exception \(q_0\equiv3\bmod4\) is the deleted coordinate of the exact sharp matrix. Let \(G=\mathrm{Cl}(L)\) and \(j:\mathrm{Cl}(K)\to G\) extend ideals.

The norm from \(K\) to \(\mathbf Q\) represents \(\beta\) by the literal local Kummer rows, as in the no-quartic paper. Choose \(\alpha=a+b\sqrt D\) of that norm. Its principal ideal in \(K\) has the form
\[
 (\alpha)=\mathfrak A_\beta\,\mathfrak c_K/\overline{\mathfrak c_K},
 \qquad \mathfrak A_\beta=\prod_{p\mid\beta}\mathfrak p_p,
\]
where the named \(\mathfrak p_p\) are the unique ramified primes, and \(\mathfrak c_K\) is the positive side at each complementary split pair. The class \([\mathfrak c_K]^2=[\mathfrak A_\beta]\). Extending to \(L\) and dividing \(\alpha\) by \(\sqrt{17}\) removes exactly the prime factors above 17, so
\[
 j([\mathfrak c_K])=[\mathfrak c_B],\qquad j([\mathfrak A_\beta])=[\mathfrak B].
\]

Suppose an order-eight unramified character \(\Psi\) of \(L\) has \(\Psi(\mathfrak B)=-1\). Put \(\psi=\Psi^2,\ \chi_t=\psi^2\). The character \(\psi\) of order four kills every element of \(G[2]\); so does \(\chi_t\). By quadratic genus descent \(\chi_t\) comes from \(t\in F^\times\). Since it kills the relative ramified classes, the exact norm argument of the no-quartic paper shows \(N_{F/\mathbf Q}(t)\) is square as a rational number. Consequently \(\chi_t\) is trivial on \(j(\mathrm{Cl}(K))\). Indeed for an ideal prime to the finite bad places, the product of the residue symbols on its extension equals the residue symbol of \(N_{L/K}(t)=N_{F/\mathbf Q}(t)\) at that ideal; this is the finite norm compatibility of quadratic Artin symbols. Such ideals represent all classes.

It follows that \(\psi\circ j\) is a quadratic character on \(\mathrm{Cl}(K)\) which kills all its order-two classes, since any extended order-two class lies in \(G[2]\). There is only one possible nontrivial such character, namely the genus character \(\chi_\beta\) of \(K(\sqrt\beta)/K\). To see this directly use descent to \(\mathbf Q\) (conjugation acts by inversion, and ambient complex conjugation has order two), and represent a quadratic character by a rational squareclass supported on rational primes dividing \(D\). Normalize its \(q_0\)-bit to zero by multiplication by \(D\), which does not change the extension over \(K\). The sign must then be positive: the remaining primes are \(1\bmod8\), and a negative sign would give the ramified \(-1\) squareclass over \(\mathbf Q_2\), where \(K\) splits. On these positive support choices, triviality at all ramified ideal classes is precisely the deleted ordinary Laplacian equation \(L_{0,\mathrm{ret}}x=0\). At a prime in the support the stripped residue uses \(D/p\) and the omitted \(-1\) is square there, while outside support the equation is just the local symbol of the full squareclass. The literal mark gives \(L_{0,\mathrm{ret}}\beta=0\), and its rank-one correction in the \(17\)-column is the exact invertible sharp matrix. Thus the kernel is exactly the line spanned by the \(\beta\) indicator. This verifies the asserted character restriction without an assumption about an unknown class group.

Since \(\Psi(\mathfrak B)=\psi(\mathfrak c_B)=(\psi\circ j)(\mathfrak c_K)\), the only possibility for a detector is \(\psi\circ j=\chi_\beta\) with \(\chi_\beta(\mathfrak c_K)=-1\).

## 2. Evaluate that restriction without solving any conic

Write the rational norm solution as
\[
 a+b\sqrt D=(A_0+B_0\sqrt D)/C_0,\quad
 \gcd(A_0,B_0,C_0)=1,\quad C_0>0,\qquad
 A_0^2+nB_0^2=\beta C_0^2 .
\]
The denominator \(C_0\) is prime to \(n\): at any odd ramified \(p\mid n\) the norm is integral, so the element is integral, and its two rational coordinates in \(1,\sqrt D\) are integral since their ramified valuations have different parity. For \(p\mid\beta\), its order in the uniformizer \(\sqrt D\) is one. Thus \(p\mid A_0\) and \(p\nmid B_0\). Put \(A_0=\beta A_1\), giving the integral equation
\[
 C_0^2=\beta A_1^2+(n/\beta)B_0^2 .\tag{1}
\]
At an odd prime \(\ell\mid B_0\) the two integers \(C_0,A_1\) are nonzero mod \(\ell\) by primitivity and \(\ell\nmid\beta\). Equation (1) gives \((\beta/\ell)=+1\). Also \((\beta/2)=+1\) and \((-1/\beta)=+1\). Hence \((B_0/\beta)=+1\) by quadratic reciprocity. The cases \(B_0=0\) or \(A_0=0\) cannot occur because \(\beta\) and \(n/\beta\) are not rational squares (the latter has the fresh \(q_0\)).

The norm of \(\mathfrak c_K\) is the denominator of the rational trace \(2a\), as in the general conic denominator proof. Away from 2 it has the same prime valuations as \(C_0\): for an odd \(\ell\mid C_0\) (automatically \(\ell\nmid n\)), equation (1) or the original norm equation shows \(\ell\nmid A_0\) by primitivity. Therefore \(\chi_\beta(\mathfrak c_K)=(\beta/C_0)=(C_0/\beta)\), using \((\beta/2)=+1\). For \(p\mid\beta\), \(C_0^2\equiv (n/\beta) B_0^2\bmod p\). The unit \(n/\beta\) is a square there, by the actual mark. Since \(p\equiv1\bmod4\), the Legendre symbol of either square root is the same; write this value as \(( (n/\beta)/p )_4\), equivalently the value of \((n/\beta)^{(p-1)/4}\bmod p\). We conclude
\[
 \boxed{\chi_\beta(\mathfrak c_K)=
         \prod_{p\mid\beta}\left(\frac{n/\beta}{p}\right)_4 .}\tag{2}
\]
This exact gate requires only exponentiation in the known \(\beta\) residue fields, not class-orbit or norm-conic calculation.

If (2) is \(+1\), no order-eight unramified character detects \(\mathfrak B\). Combining with its exact order two and fourth-power divisibility, duality of \(G/8G\) gives \([\mathfrak B]\in8G\). If the gate is \(-1\), the restriction of any detector is now specified, but the extension to an actual order-eight character is not established.

## 3. Both gate choices in the same original prime selection

With \(b,\theta,\beta,H\) fixed as above, only the fresh shared \(q_0\) remains to be chosen. For each \(p\mid\beta\) its old quadratic symbol is fixed by the retained local mark and 2-Selmer matrix. Thus \(Hq_0\bmod p\) must be square, but the two quartic signs on nonzero squares both occur (a cyclic group of order divisible by four). Choose a refined residue \(q_0\bmod p\) at one such \(p\) to prescribe the product in (2), holding all other rows fixed. The other CRT conditions on the companion support, helpers, and \(q_0\equiv7\bmod24\) are untouched. A fixed refined CRT residue class therefore realizes either gate by Dirichlet, with \(q_0\) arbitrarily large. This is a change of the last helper, not a change of original \(b\), conductor root signs, or prescribed finite selector matrices.

The exact conductor-16 Eisenstein ring-class ray for the genuine 17 intersection can be retained in this refinement. Its generalized dihedral field is ramified only at 2 and 3 and has elementary 2 abelianization, so its intersection with the full rational CRT field lies in \(\mathbf Q(\zeta_{24})\). The refined odd residues do not change the previous checked compatibility there. Chebotarev thus still yields both gate options even on that intersection subfamily.

There is also a constructive sharpening of the conic input itself. In the real quadratic field \(E_\beta=\mathbf Q(\sqrt\beta)\), each helper prime and \(q_0\) splits because the actual mark is a local square at these primes. Choose one \(E_\beta\)-prime above each helper and multiply them into \(\mathfrak h\) of norm \(H\). In the narrow Hilbert class field of \(E_\beta\), require the prime over \(q_0\) to have narrow class \([\mathfrak h]^{-1}\). This imposes a legitimate Chebotarev refinement of all the same rational CRT choices, including the quartic gate. Indeed the narrow class field is generalized dihedral over \(\mathbf Q\), unramified at finite rational primes outside \(\beta\). Its maximal abelian subextension over \(\mathbf Q\) is elementary 2, hence all its quadratic subfields are supported on products of primes of \(\beta\) (all are \(1\bmod4\), and adding a negative sign would ramify at 2). Restriction to this subextension depends only on the rational norm symbols there. By the exact old β-row constraint, \((Hq_0/p)=+1\) for all \(p\mid\beta\); this exactly matches the inverse class of \(\mathfrak h\) on the common cyclotomic part. Any extra finite primes in the rational CRT are outside that common field. If the conductor-16 Eisenstein requirement is included, the two class fields are disjoint over \(\mathbf Q\) since their finite ramification supports are disjoint; their combined abelian part is the product of the two corresponding abelian parts. Hence the two checks remain sufficient for the same joint Chebotarev selection. For either generalized dihedral field one can take the conjugate prime if the inverse representative occurs.

We may therefore arrange \(\mathfrak h\mathfrak q_0=(C+V\sqrt\beta)\) with a totally positive integral generator of norm exactly \(Hq_0\). This gives
\[
 C^2-\beta V^2=Hq_0,\qquad
 N_{K/\mathbf Q}\left(\frac{\beta V+\sqrt D}{C}\right)=\beta .
\]
It produces the norm solution with coefficient one in the numerator of the \(\sqrt D\)-term, for the same exact selected first arm. Neither a particular numeric prime nor a separating character of order eight is asserted. The remaining sufficiency question is whether the prescribed \(\chi_\beta\) restriction can be realized by a quartic character of \(L\) killing \(G[2]\), or equivalently whether \([\mathfrak B]\) survives in \(G/8G\) for one of the gate-\(-1\) selections.

### Source dependencies

- *No quartic class character can detect the base arm's marked sign*, exact paper **f50c02fb01ca1b099bcd7c7a6947a2b76674ce1e7d9e4a7369c94d7717a29bdd**, supplies the actual matrix, rational norm and transferred quadratic character.
- *A genuine marked CM intersection at 17 after an admissible final prime refinement*, exact paper **06ba1eb579ce92bfeffeedcab4ef2fa3e239d461dee25828a00334bf94027ea5**, supplies the separate Eisenstein ring-class refinement.
- [Cox, §9](https://www.math.utoronto.ca/~ila/Cox-Primes_of_the_form_x2%2Bny2.pdf) and the standard ideal-class Artin map describe the generalized-dihedral class-field restriction used here; for the narrow real class field the same inversion follows immediately since the norm of an ideal is generated by a positive rational integer.
