# Both lift norms and a negative Cassels sign at every allowed contact profile

**Scope.** Fix any actual seven-prime detector squarefree profile \(\beta=17p_0p_1p_2p_3p_4q\) allowed by the [linear-q contact theorem](../../joined-work-20261120/linear-denominator-prime-small-marked-selmer-r1/ACTUAL-LINEAR-Q-MARKED-SEL2-WITH-FEWER-AUXILIARIES.md), in either contact phase. This paper constructs infinitely many **numerical Ready poles** with **that exact** \(\beta\), with depth one at the actual six contact primes, and with a certified nonzero marked \(k=0\) Cassels pairing. The two lift norms hold simultaneously. These poles are not asserted to be outputs of the original fold. The companion \(\theta\) is allowed to vary, not the fixed \(\theta\) of an existing literal pole. This is an exact obstruction to one direction at the constructed poles, not a rational-point result, full PointPair obstruction, or selected-rank proof.

## 1. Two identities; no factorization of the new C or B

Let \(t,k>0\) be odd integers and set
\[
 f=t^4-t^2+1,\quad a=12tk,\quad A=\beta a^2,\quad D=12\beta k^2-f,
 \quad C=D^2-A,\quad B=A+3D^2.
\]
Then \(A=12t^2(D+f)\) and by expansion
\[
 C=(D-6t^2)^2-3(2t(1+t^2))^2,\qquad
 B/3=(D+2t^2)^2+(2t(1-t^2))^2 .
\]
These are simultaneous integral identities on the **same** A,D. Choose the parameters below so \(A,D\) are reduced and the first norm is primitive. Then the [exact full-lift theorem](../ct-original-k0-first-character-r1/ACTUAL-K0-FIRST-CHARACTER-AND-EXACT-LIFT.md) applies to the literal \(k=0\) Jacobian of that numerical pole. It certifies that \(\eta=(3\beta,-1,-3\beta)\) is a genuine full 2-Selmer class and that its marked bit is \((3\beta/D)\). Here \(k\) used as an integer in the displayed construction is **not** the norm direction \(k=0\) of the quartic.

## 2. The two exact CRTs

Choose any one of the six contact primes, \(p_*\). All six are \(1\bmod408\), hence \(1\bmod24\) and \(1\bmod17\), and \(p_*\ge409\). The separable quartic \(F(T)=T^4-T^2+1=\Phi_{12}(T)\) takes a **nonzero nonsquare** value in \(\mathbb F_{p_*}\). For example the smooth completion of \(Y^2=F(T)\) has genus one and two rational infinity points (leading coefficient 1). If every nonzero value were a square, there would be at least \(2p_*-4+2\) rational points, violating the Hasse bound \(p_*+1+2\sqrt{p_*}\) at \(p_*\ge409\). Separability holds since \(p_*\nmid12\) and \(F\mid T^{12}-1\). The resulting residue \(t_*\ne0\), since \(F(0)=1\).

Use the ordinary CRT to choose \(t>0\) with
\[
 t\equiv t_* \pmod{p_*},\qquad t\equiv1\pmod{6\beta/p_*}.
\]
In particular t is odd, prime to 3 and every prime of β, and \(f\) is a unit at all those primes. Its character is negative at \(p_*\), positive at every other prime of \(3\beta\). The 17 residue is explicitly \(t\equiv1\), irrespective of the selected phase. Also \(f\equiv1\bmod t\), \(f\equiv3\bmod(1+t^2)\), and \(3\nmid1+t^2\); hence \(\gcd(f,t(1+t^2))=1\).

The second CRT can be implemented **without factoring** t or \(1+t^2\). Put
\[
 k_0=t\cdot\left((1+t^2)/2\right)_{\!\mathrm{prime\ to}\ \beta},
\]
where the subscript removes the entire part supported on \(\beta\), for example by repeated gcd. The factor \((1+t^2)/2\) is odd (for odd t), and \(k_0\) is positive, odd, prime to \(3\beta f\). Choose \(k=k_0(1+6\beta f\,j)\), with positive \(j\) as large as needed. Then k is a unit at \(2,3,\beta,f\) and has every odd prime divisor of \(t(1+t^2)\) not in \(\beta\). This is the required second set of residue conditions; it is compatible even if the two numbers \(1+t^2\) and \(\beta\) have common factors.

## 3. Primitivity, Ready, and the sign

For \(\gcd(A,D)=1\), check a prime of A. At 2 and 3, \(D\equiv-1\) modulo p. At a prime of \(\beta\), \(D\equiv-f\) is a unit. At an odd divisor of t, k is divisible there and \(D\equiv-f\equiv-1\). At any remaining divisor of k, \(D\equiv-f\) is a unit by \(\gcd(k,f)=1\). This covers all prime factors of A. For the first norm, put \(U=D-6t^2,\ V=2t(1+t^2)\). U is odd. At a prime of t it is \(-1\); at an odd p dividing \(1+t^2\), it has residue \(3(4\beta k^2+1)\). For the latter primes p is not 3 and either \(p\mid\beta\) or \(p\mid k\), so this residue is 3. Thus \(\gcd(U,V)=1\). For large j, \(D,U>0\) and \(2U-1>3V^2>0\); therefore the actual C lies strictly between \((U-1)^2\) and \(U^2\), so is **positive nonsquare** and \(0<A<D^2\).

Define \(b=17A/D^2\). It lies in \((0,17)\); its reduced denominator is the square \(D^2\) since D is coprime to 17 as above. Its depths at \(2,3,17\) are exactly \(4,2,2\): t,k are odd, prime to 3 and 17, and \(17\mid\beta\) once. Its three local square guards hold because \(b=17\beta (a/D)^2\), and \(17\beta\) is square locally: odd unit \(1\bmod8\) at 2, unit \(1\bmod3\) at 3, and stripped square unit \(\beta/17\bmod17\) at 17 (all contacts are \(1\bmod17\)). The squarefree class of \(\mu=b/17\) is exactly \(\beta\); at each contact \(\mu\) and b have depth one. Since A grows quadratically and \(D^2\) quartically in k, the resulting positive b values tend to zero and include infinitely many distinct ones.

Finally \(D\equiv-f\bmod3\beta\) and \(D\equiv3\bmod4\) (f is \(1\bmod4\) for t odd). For positive odd coprime \(D,3\beta\), quadratic reciprocity for Jacobi symbols therefore gives
\[
      \left(\frac{3\beta}{D}\right)
      =\left(\frac{-f}{3\beta}\right)\left(\frac{-1}{3\beta}\right)
      =\left(\frac{f}{3\beta}\right)=-1.
\]
There is exactly one negative residue row by construction. All exponents and denominators are the ones of the reduced A,D, not of a later scaled representative. The chosen **same** primitives therefore give the full lift and a rigorous marked Cassels obstruction on both positive and negative allowed contact-profile phases, with no appeal to the October pointwise rank converse.

## 4. What this does and does not decide for fixed squarepairs

Both simultaneous norms and the sign have a direct construction once the companion is allowed to vary. The construction does not force \(C\) to have a user-specified \(\operatorname{sf}(C)=\theta\). Indeed if that prescribed θ has a prime nonsplit in \(\mathbb Q(\sqrt3)\), no representative of that squareclass can have a primitive C norm at all. Even if all θ primes split, our construction imposes no equality to that particular θ or to the literal original formula \(b_j(h,t_{\rm source})\).

The two pure-integer replay inputs are the earlier allowed contact-profile controls in the two phases. They verify every modulus choice and primitive gcd, both norm identities, exact local Ready valuations/units, and the negative Jacobi sign. The controls and the constructed family are numerical arithmetic instances, **not** actual detector outputs.

Replay: python3 -B verify_two_norm_contact_profiles.py | cmp - EXACT-TWO-NORM-CONTACT-PROFILES.json. No Lean build, external write, or large factoring search.
