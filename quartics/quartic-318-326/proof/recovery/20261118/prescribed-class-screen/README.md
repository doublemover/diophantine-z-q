# Prescribed first squareclass, marked complement and the actual source screen

**Scope.** The fixed 9145 family from the preceding packet cannot contain
*any* of the three prime-selected contact poles or the scalar pole at an
integer input. We give new positive results for every prepared first
squareclass, including literal scalar input zero, and for neighborhoods
of a prescribed prepared pole. The surviving gap is the exact complementary
squareclass at that specific pole, not just local or real compatibility.
No circuit assignment, rank theorem, unrestricted point-pair producer,
Lean compilation, manuscript change or release acceptance is claimed.

### 1. Two unconditional exclusions for the previous sample

In the original nonzero-label, positive and prime-selected contact setting,
`MergedContactPrimePattern318.all_positions_prime` and `row_distinct`
make the row product a squarefree product of **five** distinct primes.
`ActualContactPrimeSquareclasses318.witness` identifies it with the
squareclass of the corresponding actual positive pole, with the nonzero
square factor of `squareFactor_ne`. Repetitions *between* rows change
nothing. This cannot be 9145=5·31·59, with only three prime factors.

For the scalar, `ActualFourPoleClassMatching318.scalar_factor` gives squareclass
11·inputR(a) whenever the pole is nonzero, for integer a.
`ScalarPolePreparation318.integerR_cast` identifies this with the literal
integer polynomial in x=a+a². From constant through quartic its coefficients
are congruent to (43,0,0,0,0) modulo 73. Thus 11·integerR(a)≡35≡20²
mod 73 is always a nonzero square; 9145≡20 and 20³⁶≡−1 mod 73. As both
representatives are units, a putative rational square ratio would reduce to
a square modulo 73. This excludes the sample simultaneously for all a, not
just for tested inputs.

### 2. Uniform construction with prescribed first class

Fix positive squarefree m which is a local square at 2,3,17, so these primes
do not divide m. Any nonempty finite set of distinct primes Q can be marked
provided q∤102m and c=m/17 is a nonzero square modulo each q in Q. Given a
finite avoidance set F and no supplied marker, a suitable fresh q always
exists without a prime-distribution assumption: let H be a positive multiple
of 102m and all primes of F, and take any prime divisor of 17mH²−1>1.
It avoids H and 17m, and (mH)²≡c mod q. This method can also add a fresh
marker to a previously supplied finite set.

By CRT choose a positive integer r with v2(r)=3, v3(r)=2, r≡1 mod 17
and r≡1 mod every prime of m. At each marked q prescribe vq(r²−c)=1:
among the q lifts modulo q² of a nonzero root of c modulo q, exactly one
makes the difference zero modulo q² (the derivative 2r is a unit).
All congruences use coprime moduli. Increase r in its residue class until
r²>9c. Define

    z=4r/(r²+3c),  u=2(r²−3c)/(r²+3c),  b0=m z²,
    C=b0/17,       d=1−C=(r²−c)(r²−9c)/(r²+3c)².

Then 4−3b0/17=u², and positivity and 0<d<1 follow directly. At each
q in Q, the factors r²−9c and r²+3c reduce to −8c and 4c (units).
Thus vq(d)=1. In particular d is a nonsquare. At p|m, z is a unit,
because r≡1 mod p and c≡0; this also gives d≡1 mod p.
At 2 the denominator of z is odd; at 3 it has valuation 1; at 17 it has
valuation −1 because c has valuation −1 and r is a unit. Therefore b0
has depths (10,2,2). The numerator and denominator arguments include m=1.

In the exact PointPair equations write B0=17b0, V0=B0²d and F_n(x)=
x(x−n)(x+3n). The rational seed E0=B0, s0=B0, y10=0, y20=B0⁴b0u works:
the second right side is B0⁹(1−d)(1+3d)=y20². The second ordinate is
nonzero. This uses the *older* one-torsion criterion at a deliberately
constructed seed, not at the target pole.

On the conic C X²+d Z²=1, use the secants through (1,1):
X=(dλ²−2dλ−C)/(C+dλ²), Z=1+λ(X−1). For XZ≠0 the actual pole b=b0X²
has class m and actual complement dZ². The preceding packet's exact
homogeneity transport supplies the same-E rational pair at this b:
E=E0X², s=s0X²Z, y1=0, y2=y20X⁹Z³. The ordinates satisfy the source
structure, which expressly permits first ordinate zero. All marked q still
have odd valuation in the complement, not necessarily valuation one
after the final square factor.

Take λ=16+M j/L^k with M=32·3·17·m and L=M+1, so denominators are
coprime to M. At 2 the respective minima in the numerator and denominator
of X are 5 and 8, giving v2(X)=−3; at 3,17 both λ and λ−2 are units,
C≡0, and X is a unit. At p|m, C≡0, d≡1, λ≡16 is a unit; X is integral.
Thus b has exact depths (4,2,2), is locally square at the three designated
places, and has square reduced denominator: at p|m its valuation is
nonnegative, and at every other prime it is even. These slopes are real
dense by their vanishing mesh, and for any target value t∈(0,17) the real
conic point X=−sqrt(t/b0), Z=sqrt((1−t/17)/d) has a finite secant slope.
Continuity, deleting the finitely many zeros XZ=0, proves real density in
(0,17) at the exact depths. No claim about the original indexed orbit is used.

### 3. Joint approximation to a specified actual pole is still not equality

Let b* be any particular prepared rational pole (0<b*<17, square reduced
denominator, local squares at 2,3,17, depths ≥3,1,2). Write b*=m w*² for its
positive squarefree representative, w*>0. Then m meets §2. Let S be
{2,3,17} together with all primes of m. D*=1−b*/17 and d from §2 are
squares in every Qp for p∈S: at 2 they are 1 mod 8; at 3,17 they are 1
mod p; at p|m, v_p(b*) is odd and must be positive by square denominator,
and v_p(b0)=1, hence both complements are 1 mod p. They are positive over R.

Take the *same* rational X*=−w*/z (<0) at all these places and at infinity.
Choose local Z_p²=D*/d and a real such root. Then C X*²+d Z_p²=1 and each
λ_p=(Z_p−1)/(X*−1) is finite. The secant denominator is nonzero there:
writing Z_p=1+λ_p(X*−1) in the conic gives
(X*−1)(C+dλ_p²)=-2(C+dλ_p). If C+dλ_p²=0, then simultaneously
C+dλ_p=0; the latter would give C+dλ_p²=C+C²/d=C/d≠0. This deals with
possible p-adic isotropic slopes, not only the positive real denominator.

Approximate all λ_p and the real λ∞ simultaneously by rationals. For a
direct proof, clear denominators of the finitely many p-adic targets by a
fixed positive integer H. For any required precision prescribe integral
residues of Hλ modulo sufficiently large powers of those p; use one CRT
class. To meet the real bound as well, choose a denominator L^k with
L>1 coprime to these p and solve the congruences for L^k Hλ instead.
Possible real λ then have mesh P/(H L^k), where P is the fixed product of
prime-power moduli; taking k large meets any real interval. This proves
the simultaneous approximation without a rational elliptic-rank assumption.
By continuity and nonvanishing, the resulting b and conic coordinates are
arbitrarily close at all requested places. In particular b has the *target's*
valuations there once the approximation is sufficiently close. At primes
of m, w=zX stays integral because w*=−zX* is integral there. The square
denominator and actual rational pair persist as in §2.

Crucially, choose a fresh marked q outside S and the finite numerator/
denominator support of D*. Then D* has valuation zero there while every
constructed complement dZ² has odd valuation. Thus even with arbitrary
simultaneous approximation at the listed places, and *exactly equal* first
squareclass, this deliberately constructed family cannot hit the given
target or supply its second class. Repeating with q outside every earlier
seed complement's support produces infinitely many distinct complement
squareclasses for the same m. This identifies precisely why such local
matching cannot serve as a universal original point-pair producer. It does
not prove that rational point-pairs at the true target fail to exist.

### 4. Literal source-class diagnostic and reproducibility

At integer input a=0, 11·integerR(0)=4·12036405179807305. Its squarefree
representative is 5·11·163·661·733·1489·1861 (1 mod 8,3,17).
FINITE-REPLAY.json constructs a rational pair with this exact first class,
three odd complement markers and depths (4,2,2). There is no claim that
the computed b equals the scalar circuit output at any common index.
At a prime-selected prepared contact row, put m equal to its five-prime
row product; the same construction applies *without an explicit numeric*
fifteen-prime tuple. Nothing here manufactures such a tuple.

Historical sources: at a0950ac7, in the original fifteen-position
reconstruction and r155 proof sources, see the exact declarations named
in §1, NormalizedPolePoints318.PointPair, OneTorsionPoleFamily318.certificate,
PositiveSquareclassPole318.exists_certified_pole (square complement),
ActualPreparedPoleSquarefreeClasses318.positive_squarefree and
ActualFourPolePreparation318.actual_four_descent. Quartic_v10.tex's
preparation-zero bridge is the local preparation standard. No replacement
for its fixed target is asserted here. The preceding prepared-pair packet
supplies the transfer algebra; this packet adds the fresh-prime, exact-class
construction and the two actual-source exclusions. The previously reviewed
two-nonzero-ordinate result remains specialized to 9145; the new general
argument does not promise two nonzero ordinates.

Run `python -B verify.py` to reproduce FINITE-REPLAY.json; examples, including
m=1, the old class and the actual a=0 class, are exact finite tests, not
proof of the quantified assertions. Source-level research only.
