# Exact oriented square-root-five descent for the same Γ

Keep the [literal sparse Γ](../ct-original-scalar-mestre-sparse-quartic-r1/LITERAL-GAMMA-SPARSE-QUARTIC-AND-BOUNDED-CRT.md), the fixed squarefree
\(\beta=5\cdot11\cdot17\cdot163\cdot661\cdot733\cdot1489\cdot1861\), and the positive squarefree class \(\theta\) of the exact source \(\delta\). The factorization of \(\theta\) is not supplied here. This gives a finite oriented norm criterion if one can supply that factorization, and determines the coefficient partition uniquely from the orientation; the final two quadrics are a genuine remaining rational point problem, not presumed soluble.

## 1. Ideal descent and exact inverse

Set \(\omega=(1+\sqrt5)/2\), \(R=\mathbf Z[\omega]\), and \(U=2+\sqrt5\), so \(U^2=5+8\omega\), \(\overline U^2=U^{-2}\). In the sparse primitive chart \(M=gX\), \(\beta=ge\), set
\[
 A=gX^2-eU^2N^2,\qquad
 A\overline A=g^2X^4-18\beta X^2N^2+e^2N^4=\theta Y^2.            \tag{1}
\]
Use either reciprocal primitive chart as necessary to arrange \(A,\overline A>0\): the reciprocal takes \(A\) to \(-U^2\overline A\). The two real signs always agree by (1).

The factors in (1) have coprime ideals in \(R\). Indeed \(A-\overline A=-8e\sqrt5 N^2\). At any prime ideal not above 2 or 5, if both factors vanished then the rational prime below would divide \(eN^2\) and \(gX^2\). This contradicts \((g,e)=(gX,N)=(e,X)=1\). At 5, the unique prime sees \(U^2\equiv4\); exactly one of \(g,e\) is divisible by 5 and its complementary variable is a unit, so neither factor vanishes. At 2, \(g\equiv e\pmod8\) because \(\beta\equiv1\pmod8\); if both \(X,N\) were odd, the expression
\[
 (gX^2-eN^2)^2-16\beta X^2N^2
\]
would have 2-valuation 4 and stripped unit \(3\bmod4\), contrary to the known square class of \(\delta\) at 2. Thus exactly one of \(X,N\) is even and \(A\) is a unit at the unique prime over 2. Similarly \(3\mid XN\) follows from (1) mod 3 and the known square class of \(\delta\) there; this is compatible with primitivity.

The ring \(R\) is norm-Euclidean: rounding the two coefficients in \(1,\omega\) leaves real rational errors \(x,y\) of absolute values at most \(1/2\), so \(|x^2+xy-y^2|\le3/4\). The quadratic field ring of integers is indeed \(R\) since the discriminant is 5. Each rational prime factor of \(\theta\) must split here: a nonsplit odd-depth rational prime would have no permitted ideal exponent by coprimality, and 2 and 5 are excluded. For each rational \(p\mid\theta\), choose one of the two prime ideals over it, and a totally positive generator \(\pi_p\) of norm \(p\). This normalization is possible: multiply a generator of negative norm by \(\omega\) (norm \(-1\)), then if necessary by \(-1\). Any totally positive unit is a square: the unit group is \(\{\pm\epsilon^j\}\) by the real quadratic unit theorem, its generator has norm \(-1\) since \(\omega\) does, and an even power can be given positive sign at both places only by the plus sign. Therefore (1) with primitive coordinates and both factors positive is equivalent, over all orientations, to
\[
                 gX^2-eU^2N^2=\alpha z^2,\qquad
                 \alpha=\prod_{p\mid\theta}\pi_p,\quad z\in R .   \tag{2}
\]
Norming (2) returns exactly (1), with \(Y=\pm N_{R/\mathbf Z}(z)\), hence the old explicit inverse and raw PointPair. Neither the orientation of any unseen prime nor the existence of \(z,X,N\) is asserted.

Writing \(\alpha=a+b\omega,\ z=v+w\omega,\ J=v^2+w^2,\ K=2vw+w^2\) makes (2) literally the two integral quadrics
\[
 gX^2-5eN^2=aJ+bK,\qquad -8eN^2=bJ+(a+b)K.                     \tag{3}
\]
The rational analogue is equivalent after clearing all four denominators at once and checking \(\gcd(gX,N)=\gcd(e,X)=1\); the integral formulation already demands these conditions. This is a degree-raising descent, not a pair of independent soluble conics.

## 2. At literal known places the orientation fixes the entire partition

Use the ordered \(\beta\) prime list above and write \(\lambda_i=1\) if its \(i\)-th prime divides \(g\). At \(p=5,11,661,1489,1861\), sample the Legendre bit of \(\alpha\) in the residue field at one place over \(p\); at 5 there is just one place, and at the other four the bits in the two places match since \(N(\alpha)=\theta\) is a square unit there. Reduction of \(A\) gives the bit of \(g\) when \(p\nmid g\), and that of \(-e\) when \(p\mid g\); \(U^2\) does not contribute. The resulting \(g\)-row has off-diagonal entries \([(\tfrac{q}{p})=-1]\) for \(\beta\) primes \(q\ne p\), and diagonal \([(\tfrac{-\beta/p}{p})=-1]\). At the other three \(\beta\) primes, 5 is nonsquare, and the unit condition is automatic because \(\theta\) and the rational classes \(g,-e\) have square residue norms there.

At a known \(p\mid\theta\), put \(\tau=\sqrt5\bmod p\) in the place selected by \(\pi_p\), so \(A(\tau)=0\). The other place has
\[
 A(-\tau)= e N^2\big((2+\tau)^2-(2-\tau)^2\big)=8eN^2\tau\pmod p .
\]
The unit equation is thus \((\alpha(-\tau)/p)=(8\tau/p)(g/p)\), because \(\beta\) is a square at this place. The five \(\beta\) rows, then the literal visible \(\theta\) rows in increasing order, are the nine masks
\[
       45,\ 164,\ 96,\ 116,\ 170;\qquad 60,\ 132,\ 12,\ 0 .
\]
The first eight have rank eight. For any oriented \(\alpha\) they therefore give a *unique* possible partition \(g\), with no enumeration over the former 256 partitions.

The last zero row, at \(p_*=16782959\), fixes one orientation bit. Holding every other \(\pi_p\) unchanged, flip the chosen \(\pi_{p_*}\) to its conjugate. The nonzero residue value of that generator at the place opposite itself is unchanged, and the Legendre bit of the remaining factors at the two switched places agrees: their norm is \(\theta/p_*\), whose residue class equals that of the actual stripped \(\delta/p_*\). The compact source certificate gives \(\delta/p_*\equiv13715188\), a square unit. In contrast the right bit \((8\tau/p_*)\) flips, since \(p_*\equiv3\bmod4\). Exactly one of the two orientations satisfies this row. No unseen support data are needed for this logical reduction; the actual value of the forced orientation is not yet known.

Thus, given the exact positive split factorization of \(\theta\), one can enumerate orientations on the remaining prime factors, force the last visible orientation by this one character, solve the full-rank linear system once, and test the two explicit quadrics (3). The four visible norm generators and rank calculation are replayed. Neither the missing split factorization, a rational intersection point, an actual obstruction to (3), nor any rank claim follows. A synthetic fixture confirms an actual nontrivial square factor in (2); it is not an original pole.
