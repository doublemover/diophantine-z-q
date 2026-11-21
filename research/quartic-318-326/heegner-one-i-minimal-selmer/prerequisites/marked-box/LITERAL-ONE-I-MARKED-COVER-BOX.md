# A different target: the actual one-I marked genus-one cover

The base \(q=119851\), \(p_I=114649\) in the fixed actual scalar
selection has

    P = p_I q = 13,740,797,299,
    β = 204,618,888,056,724,185,
    d = β P = 2,811,626,664,334,219,040,035,976,315.

This is independent of computing the oriented theta coefficient.
It only addresses the original marked base class \((β,1)\);
there is no claim on the companion or seven-I retune.

The true genus-one cover in projective coordinates is

    U² − β Z² = P T²,      W² − U² = 3 P T².

Every rational point here has \(T\ne0\): otherwise
\(U^2=\beta Z^2\) and \(W^2=U^2\), and the nonsquare β forces all
four coordinates zero. With \(T\ne0\), both U,W are nonzero
by positivity, and Z is nonzero since P is nonsquare.
The map to the actual \(E_d:y^2=x(x-d)(x+3d)\) is

    x = β U²/T²,    y = β² U Z W/T³.

Its \(x\) squareclass is β, while \(x-d=β²Z²/T²\) is a square,
giving the exact original mark. Conversely any nonexceptional
rational point with those two classes supplies these coordinates.
Good reductions at 7 and 53 have cardinalities 8 and 52,
respectively, by the exact finite counts. Prime-to-place torsion
injectivity and the cross exclusions \(7\nmid52\), \(53\nmid8\)
bound the entire rational torsion by \(\gcd(8,52)=4\).
The actual four rational 2-torsion points attain that bound.
Since y≠0 over this cover, a rational point would give genuine
base nontorsion without any Heegner trace or residual coefficient.

Put \(A=(W+U)/T\ne0\), and then
\((W-U)/T=3P/A\). Eliminating U gives exactly

\[
 \beta V^2=(A^2-P)(A^2-9P),\qquad V=2AZ/T.
\]

The four quartic branch roots are distinct. Its rational finite
points have \(A\ne0\) (else β would be square); the reciprocal
chart also has no rational points at infinity since the leading
term is a nonsquare. This is equivalent to the cover above.
Writing \(A=a/b\) primitive, one may take \(a,b>0\), by the
symmetry in A and the sign convention on the denominator.
The product \((a^2-Pb^2)(a^2-9Pb^2)\) must be β times an
integer square: \(\beta(b^2V)^2\) integral and β squarefree
imply \(b^2V\) is integral. At each of the eight β primes,
\(b\) must be a unit and \(a/b\) a root of the product mod
that prime. There are exactly four distinct roots at each
prime (checked), hence 65,536 exact possible residue classes
\(r\bmod\beta\), giving the integer lattices
\(\{(a,b):a\equiv r b\bmod\beta\}\).

The script enumerates **all** primitive pairs in those lattices
for \(1\le a,b\le10^9\). An exact two-dimensional Gauss basis
\(u,v\) has determinant ±β, so if \((a,b)=m u+n v\), then
\(|n|\le\lfloor 10^9(|u_1|+|u_2|)/\beta\rfloor\). For each n the
two coordinate inequalities give a complete integer interval
for m. The primitive root class is unique by the denominator
guard, so no double count. At height bounds \(10^7,10^8,10^9\)
there are respectively 11, 1,377, 139,088 primitive pairs
passing all root congruences, all with positive product in this
range, none with the required complete square product. The
last box runs in about 1.3 seconds. This is a strict bound on
the height of A for any solution, not a proof that the torsor
has no rational point or any assertion about rank.

A more meaningful next arithmetic search is to split the two
integer squareclasses and run a focused descent, not simply
inflate this box. If \(F=a^2-Pb^2\), \(G=a^2-9Pb^2\), then
\(\gcd(F,G)\mid 8P\) by primitivity. Thus in a solution

    F = ε B₁ D U₁²,       G = ε (β/B₁) D U₂²,

for a divisor \(B_1\mid\beta\), squarefree \(D\mid2P\) and a
common sign ε. There are at most 4,096 pairs of such
quadrics. For \(\ell\mid P\), the prime belongs to D exactly
when \(\ell\mid a\) (both factors then have valuation 1);
and 2 belongs to D exactly when a,b are both odd
(\(P\equiv3\bmod8\)). These conditions give a finite list
for further local descent/height minimization. None of the
subcovers has been shown to have a point. This target is
separate from Joined's scalar-norm and q1041427 lanes.

    python3 -B check_one_I_marked_cover_box.py | cmp - EXACT-ONE-I-MARKED-COVER-BOX.json
