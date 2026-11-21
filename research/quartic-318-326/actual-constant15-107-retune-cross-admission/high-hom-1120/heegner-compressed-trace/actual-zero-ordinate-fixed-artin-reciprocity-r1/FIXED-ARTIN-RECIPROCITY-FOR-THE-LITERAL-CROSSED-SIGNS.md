# Exchange both literal crossed Cassels signs for fixed-field Artin signs

Keep the actual linked \(c>0,\ \mu=\beta c^2,\ \delta=1-\mu,\ \theta=[\delta]\), and define \(T=131\cdot6551\cdot2470991\cdot16782959,\ U=\theta/T\), as in the [actual positive boundary receiver](../actual-zero-ordinate-aggregate-norm-admission-r2/). There is no assumption about the number of prime factors of \(U\). The positive two-descent tests have second coordinates
\[
 s_1=2952271997968816765,\qquad s_2=5566083893370034.
\]
The original Cassels signs require the two characters \((s_j/D_{\rm exc})\) of the still unknown exceptional denominator support. The following removes the need to acquire any crossed denominator prime if the actual hidden **numerator** support (or a certified fixed-field ideal Artin sign for it) is available. Neither such support nor its signs are supplied here.

## 1. Two explicit fixed norms and the local symbol transport

In \(k=\mathbf Q(\sqrt\beta)\), put \(\gamma=1+c\sqrt\beta\), of norm \(\delta\). Two fixed algebraic integers \(\sigma_j=x_j+y_j\sqrt\beta\) have
\[
 \mathrm N_{k/\mathbf Q}\sigma_j=s_j z_j^2,\qquad
\begin{array}{c|rrr}
j&x_j&y_j&z_j\\ \hline
1&31859917667562016618135&59323292900802&9995282212057\\
2&131334033162619006246327&275139103369479&562104197612846
\end{array}
\]
with \(\gcd(x_j,y_j,z_j)=1\). These are directly checked integer identities. At every odd prime \(p\nmid \beta s_j\) all prime-ideal valuations of \(\sigma_j\) over \(p\) are even. For a split \(p\mid z_j\) the two conjugates cannot both vanish: otherwise \(p\mid x_j,y_j,z_j\). The valuation in its one vanishing arm is then \(2v_p(z_j)\). Inert \(p\mid z_j\) likewise cannot occur, since vanishing in the quadratic residue field would force both coefficients to vanish. Thus primes of \(z_j\) away from the fixed support cause no extra odd ramification and do not have to be factored.

Apply the quadratic Hilbert product formula over \(k\) to \((\gamma,\sigma_j)\). At any odd denominator prime \(p\nmid\beta s_j\), both components, or the inert component, have \(v(\gamma)=v_p(c)=-e\). For each component strip the even valuation of \(\sigma_j\). In a split place the product of the two normalized residue symbols is \((s_j/p)\) by the norm identity. In an inert place the quadratic residue symbol in \(\mathbf F_{p^2}\) equals the Legendre symbol of the residue norm, also \((s_j/p)\). Thus the total contribution at such a denominator prime is exactly \((s_j/p)^e\). At an integral place \(p\nmid2\beta s_j\), a nonunit \(\gamma\) can occur only above a split prime, on the single arm \(\sqrt\beta\equiv-1/c\bmod p\), with valuation \(v_p(\delta)\). It contributes only when that valuation is odd, with the quadratic symbol of the stripped \(\sigma_j\)-unit on that arm. Other integral good places contribute one.

For \(p\mid U\) define \(\chi_j(p)\in\{\pm1\}\) as this one-arm symbol. The extension \(k(\sqrt{\sigma_j})/k\) is unramified at every such prime ideal; the same sign is its quadratic Frobenius. The orientation is literal, not a free choice unless \(s_j\) splits modulo \(p\). All primes \(p\mid U\) already split in \(k\), by \(\delta=1-\beta c^2\).

## 2. Exact fixed factors for the original scalar

At \(p\mid\beta\) the ready scalar has \(c\) integral, and \(\gamma\) is a square unit at the odd ramified place (its residue is 1). At 3 its residue is 1 as well; at infinity both real embeddings of \(\gamma\) are positive. At 2 the field splits and the exact \(v_2(c)=2\) gives both \(\gamma\) values congruent 5 modulo 8. The dyadic product is therefore \((-1)^{v_2(s_j)}\). The four fixed denominator primes have \(v_p(c)=-1\) and total contribution \((s_j/K)\), for \(K=1+2448\beta=29\cdot181\cdot1346909\cdot70850399941\). They are disjoint from the two character supports.

At a visible \(\theta\)-prime the previously checked inputs are the literal \((c\bmod p,\delta/p\bmod p)\) with \(v_p(\delta)=1\):
\[
 (131,54,82),\ (6551,2194,684),\
 (2470991,722614,2223081),\ (16782959,9763981,13715188).
\]
They can also be read from the [compact source residues](../../../joined-work-20261120/rc-linked-scalar-specialization-r1/ACTUAL-THETA-MODULAR-ROWS.md), [additional prime-square controls](../../../joined-work-20261120/rc-linked-scalar-higher-descent-r2/ACTUAL-NEW-H-PRIMES.json), and [literal support replay](../actual-theta-split-scan-r1/). At the \(\gamma\)-zero arm the stripped unit is \((\delta/p)/2\); the other arm has unit 2. Lift \(-1/c\bmod p\) to a square root of \(\beta\) modulo \(p^2\) to read the two exact stripped \(\sigma_j\) units (none of the \(z_j\) vanish at these visible places). The odd Hilbert formula gives the following fixed sign table:
\[
\begin{array}{c|rrrrrr|r}
 &2&K&131&6551&2470991&16782959&\mathrm{product}\\\hline
 j=1 &+&+&+&-&-&+&+\\
 j=2 &-&-&+&+&+&-&-
\end{array}
\]
All other possible norm factors of \(\sigma_j\) at odd primes away from \(\beta s_j\) have even valuation, as above; they do not insert an unaccounted finite character. Reciprocity now yields, with literal orientation even when the test is not admitted,
\[
 \boxed{\quad (s_1/D_{\rm exc})=\prod_{p\mid U}\chi_1(p),\qquad
               (s_2/D_{\rm exc})=-\prod_{p\mid U}\chi_2(p).\quad}
\]

## 3. How to read the signs if the actual numerator support is acquired

For a genuinely admitted named test, each \(p\mid U\) satisfies \((s_j/p)=+1\) by its exact local admission equations. Then the two arms give the same value of \(\chi_j(p)\), by the norm identity; no elliptic chart or modular \(c\) evaluation is needed at these unseen primes. Take either square root of \(\beta\bmod p\), or the unit arm if a \(z_j\) prime vanishes on the other arm. This works without any bound or assumption on the number of primes. For a genuinely admitted product test \(\eta_1\eta_2\), use \(\sigma_1\sigma_2\); the product of the two arm symbols is \((s_1s_2/p)=+1\) even if the individual tests are not admitted. Since \(z_1,z_2\) are coprime, at least one arm is a unit for the product at the unseen primes.

Equivalently, if a complete factorization is unavailable, it is enough to supply an ideal of \(k\) of exact norm \(U\) with certified Artin character in the indicated quadratic extension (and independently certify admission). With the split conditions the character is independent of which prime ideal over each rational prime is used. This is a fixed-field computation, not an elliptic coordinate expansion. It does not by itself construct a suitable ideal or evaluate its Artin class from the raw circuit.

The quadratic traces cannot be replaced just by rational congruences. Each \(k(\sqrt{s_j},\sqrt{\sigma_j})/\mathbf Q\) is dihedral of degree eight: the nontrivial conjugation on \(k\) sends \(\sigma_j\) to \(s_jz_j^2/\sigma_j\); neither \(\sigma_j\) nor \(s_j\sigma_j\) is square in \(k\), by taking rational norms. The resulting conjugation on the biquadratic group over \(k\) is nontrivial. The central sign is not in its maximal abelian quotient \(k(\sqrt{s_j})\). Thus rational congruences, including auxiliary split rational quadratic characters, do not specify this sign at general rational primes splitting \(k(\sqrt{s_j})\). For example the normalization auxiliary \(1186981\) is split in the rational fields of both tests but gives \(\chi_1=\chi_2=-1\), on both arms, by the short replay. It is **not** an unseen prime of the actual \(\theta\).

The original positive Cassels row for an admitted named test is still \(- (s_j/D_{\rm exc})\); for an admitted product it is \(+(s_1s_2/D_{\rm exc})\). No actual admission, unseen Artin product, phase, exclusion of another full lift, or rational point follows without the additional certified input.

    python3 -B check_zero_ordinate_fixed_artin.py | cmp - EXACT-FIXED-ARTIN-PHASES.json
