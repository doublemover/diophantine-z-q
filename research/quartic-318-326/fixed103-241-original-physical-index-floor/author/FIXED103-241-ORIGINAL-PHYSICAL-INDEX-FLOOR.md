# Fixed 103 and 241 do not make the original discriminants small

This is a numerical lower bound on the literal source keys, not on the cost of an arbitrary proof. It concerns the original positive linear-$q$ construction with the fixed final Selmer prime 103, the fixed conductor/helper 241, and the protected 5 and 29 source refinements. It applies to both admitted fixed-conductor arms and all three detector slots. The much stronger final-anchor bound stated separately below applies specifically to the unscaled slot 190. No actual key or new point is constructed.

## 1. Two genuinely different rational prime rays

Write $B$ for the common integral slope clearing, $Q$ for the subsequent fixed Gaussian-wheel enlargement, and $c_j\ne0$ for the scale on the literal detector in slot $j\in\{190,241,292\}$. In a row put $A=|B/c_j|$ and
$$
t=\frac{u}{B^2Q^2q},\qquad p_r=u-(AQ)^2q r,\qquad
\mathcal R=\{0,-1/2,-1,1/2399,-32/407\}.
$$
All five $p_r$ and the separate order-only prime $q$ are positive distinct primes in this original key. The root $-1$ makes $A^2$ integral, hence $A$ integral; the remaining fractions force
$$A_0=2\cdot11\cdot37\cdot2399=1952786\mid A.$$
In particular the common $B$ has these divisors because $c_{190}=1$. The norm $17$ modulo 32 and norm $3$ modulo 7 from the established old Gaussian ray, together with $1$ modulo 408, give $8977\bmod11424$. The exact fixed-103 and 29,5 refinements put all six genuine primes at $1$ modulo $103,29,5$. The fixed-helper 241 ray for contacts is the Gaussian class $(0,1)$ with norm 1; the distinct order-only ray is $(1,4)$ with norm 17. Thus the rational classes are
$$
p_r\equiv14685286801\pmod{41118803040},\qquad
q\equiv29699621521\pmod{41118803040}.
$$
Their least positive prime representatives are respectively $P=96922892881$, $Q_*=70818424561$. For the contact ray the two earlier representatives have divisors $53783$ and $101$; the one earlier order-only representative has divisor $163$. The standard-library replay proves primality of the remaining two integers by trial division through their square roots. $Q_*$ is a prime floor for $q$, unrelated to the wheel integer $Q$ or the final prime 103.

As in the original clearing audit, the Gaussian ray field for modulus $m$ contains $\mathbb Q(\zeta_m)$: an ideal acts on its roots of unity by its rational norm; a principal generator congruent to 1 modulo $m$ has norm 1 modulo $m$. The **cyclotomic subfield** $\mathbb Q(\zeta_m)$ is rational abelian of conductor $m$ because here $16\mid m$. The construction takes $Q$ divisible by the rational-abelian conductor. The distinct required local primes, clearing primes and old norm channel give
$$
m_* = 16\cdot3\cdot5\cdot7\cdot11\cdot17\cdot29\cdot37\cdot103\cdot241\cdot2399
=20074055728317360\mid Q .
$$
This is only a divisor of the actual wheel enlargement; extra cutoff primes, return periods and coefficient guards can increase it.

## 2. Exact magnitude floors and what they quantify

Let $r_*=1/2399$ and $S=A_0m_*$. Since $p_{r_*}$ is the smallest contact prime in its row,
$$
d=q\prod_r p_r
\ge Q_*P\prod_{r\ne r_*}\bigl(P+S^2 Q_*(r_*-r)\bigr).
$$
Both literal twists contain $17\cdot103\cdot241\,d$; the moving fundamental discriminants $D_i=-n_i/241$ still contain $17\cdot103\,d$. All are squarefree under the admitted selector. The exact integer replay therefore gives, even ignoring all other helpers and the size of the companion,
$$
|D_i|>2.78\cdot10^{244}.
$$
No relative ordering of the source contact and order-only primes is assumed. The argument applies row by row because every detector has the same five roots, wheel and original prime residues.

Even an alternate proof retaining the same literal positive linear forms and these same rational prime rays, but **not** the Gaussian conductor divisibility, must have $41118803040\mid(AQ)^2/2$. In fact $p_{-1/2}-p_0=(AQ)^2q/2$, and $q$ is a unit at the full modulus, including at 241. Consequently $8\mid AQ$ and each odd prime of the rational modulus divides $AQ$; the additional slope denominators also give $11,37,2399\mid AQ$ by integrality of the literal contact differences, since $q$ is a prime larger than each of them. Thus $AQ\ge m_*/2$ and the analogous replay gives $|D_i|>10^{191}$. This is a conditional floor for that alternate prescription, not an assertion of its existence.

On the **actual final anchor** branch, the separate all-label anchor theorem gives for the unscaled slot only
$$
\log_2(p_{190,-1})>(3^{32767}-1)^2-8>2^{103860}.
$$
The same genuine prime divides both moving $D_i$ on slot 190 and is not the helper 241. This is therefore a lower bound in *bits* for expanded $|D_i|$ on this slot. The anchor theorem binds all labels to the same final row-287 consumer; a smaller provisional Ready experiment is no counterexample. Conversely the argument does not assert this giant anchor bound on the other two individual slots: their ratios $B/c_j$ need not equal $B$.

This argument needs no lower bound on $\theta$. The magnitude obstruction comes from $d$ alone. For perspective, the identity $1-b/17=1-dt_0^2$ as a squareclass relation with the marked $d$ does not itself force a nontrivially large $\theta$: on the rational hyperbola one can use
$$
t_0=\frac{2v}{1+dv^2},\qquad
1-dt_0^2=\left(\frac{1-dv^2}{1+dv^2}\right)^2 .
$$
A sufficiently small nonzero real $v$, of positive depth at the finitely many protected primes and at primes dividing $17d$, has $0<17d t_0^2<17$ and the fixed new small-place square-unit restrictions on the complement. This is an algebraic example only, not a literal pole or a claim that $\theta=1$ is attained by the original fold. To know the actual $\theta$, one still needs the actual common index and pole or a theorem computing its squareclass in that very family.

## 3. Consequence for class-by-class enumeration only

For each admitted $D_i$ the conductor of its primitive quadratic Dirichlet character is $|D_i|$; it is negative fundamental since dividing $n_i$ by 241 preserves its $23\bmod24$ residue and squarefreeness. The discriminant is neither $-3$ nor $-4$. [Tatuzawa, Theorem 2 and equation (1)](https://www.jstage.jst.go.jp/article/jjm1924/21/0/21_0_163/_pdf) give
$$
h(D_i)=\frac{\sqrt{|D_i|}}{\pi}L(1,\chi_{D_i})
>\frac{0.655}{540\pi}|D_i|^{269/540}>10^{118}
$$
except for at most one primitive real character. Here $\epsilon=1/540$ and $|D_i|>10^{244}>\exp(540)$, since $\log 10>9/4$; the final strict comparison uses $\pi<22/7$ and integer powering in the replay. Since $241$ is inert in the stipulated two-arm refinement, the ring class number is exactly $242h(D_i)$ by the elementary ideal class exact sequence, whose local-unit quotient has order $241+1$ and whose unit correction is one. Thus a receiver which emits one record or takes one step per oriented characteristic-zero ring class needs more than $242\cdot10^{118}$ such records or steps on at least one member of any distinct actual pair absolutely within this prescribed family. If $\theta=1$, the two arms could coincide and that fixed pair could be exceptional. The Dirichlet/Chebotarev freedom on a fresh auxiliary helper in the fixed-103 recipe still gives two distinct admissible choices at the same source, at least one nonexceptional; varying the fixed final 103 is not needed. This says nothing about the length or running time of a different aggregate certificate or of an arithmetic-circuit representation.

## 4. Smallest usable finite proof handoff

A compact arithmetic construction does not have to expand either CM orbit. Bind one actual chosen source, including the literal $(u,q)$ identities with the five contacts, prime certificates, the original common index and real/local Ready guards. Keep the same pole and source in the two arms. For a supplied $b=B_b/C_b^2$ one can bind its actual complement without factoring its whole expanded numerator or denominator: give a positive squarefree $\theta$ (with a prime certificate for each listed prime) and an integer $z$ satisfying
$$17(17C_b^2-B_b)=\theta z^2.$$
The exact local/graph selector with verified support then gives size-eight Selmer groups. A direct substitute for the two CM enumerations is **two verified rational points** on the same selected $E_{n_i}:y^2=x(x+3n_i)(x-n_i)$, one for each arm. For each, check the exact projective cubic equation and a good finite reduction with $Z$ and $Y$ nonzero in ordinary projective coordinates. The latter check shows the reduction is not 2-torsion. The split Tate place at 3 and four rational 2-torsion points give exact rational torsion of exponent two, so this one reduction proves nontorsion. The Selmer bound then forces rank exactly one and the rational Kummer image fills the entire size-eight Selmer group, including the prescribed original mark on that arm. A direct rational PointPair would avoid making the $\theta$ split at all.

There is also the existing aggregate CM substitute: a verified nonzero signed order-nine phase, or the sufficient noncube test via a fully certified anti-invariant four-ideal cubic product in the named 29 place. The support screens do not certify that product. A short modular transcript must certify the **entire** oriented lattice/divisor coefficient, not one physical intersection or a congruence of $D$ alone. The exact first family-specific missing input is an actual source witness with its own complement (or a theorem binding them existentially to the target certificates), plus a rational or aggregate nonvanishing test on both those very twists. The pilot, the fresh-prime CRT, an imprimitive weighted reference, and the existence theorem for the finite phase evaluator do not supply that input. No circuit-size lower bound or estimate on the smallest actual key is claimed.

### Exact donors

- *Linear Gaussian primes to original Ready poles*, immutable paper SHA-256 `29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0`; exact five roots, positive key, ray and conductor timing.
- The fixed 103 selector, 29 base, fixed 241 comparison, complete 5 guard, final-anchor clearing bound and prior cleared-key paper are pinned in `SOURCE-IDENTITIES.txt`.
- Primary class-number constant above was checked against printed page 164 and the two-character contradiction at pages 176–177. The machine replay is only bounded rational and prime arithmetic, not a materialization of the original source.

```sh
sha256sum -c SHA256SUMS
python3 check_fixed103_241_floor.py | cmp - EXACT-FIXED103-241-FLOORS.json
```
