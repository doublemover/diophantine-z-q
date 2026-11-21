# Independent review: absolute positive-quotient sign and simultaneous supported test control

**Verdict: both paper results pass.** This receipt binds the absolute
sign note 4edb2f200b498b0d47f8e177f6a90437940de0bf90151631316727244674c095
and author manifest 97b529620d5ebc2a62e8a1ed36580de1b81f8c867de6bfacd3f3cd65421371f0,
and the simultaneous supported quotient note ec75c1f9 / manifest
c254a8d8a681cae7343b00a582efce78c93e4514b267e6619df0252635f3b7f6.
The separate toggle arithmetic and map geometry were reviewed in
e97c82b8/7b7b0ba2.

## Absolute \(E_{bc}\) sign

Reversing the order of the two normalized arguments is harmless in
the half-integral Cassels pairing. Now the first is literally the
rational 2-Kummer class of \(T_0\) on untwisted \(E_1^{tu}\), so the
cochain \(\kappa_4(T_0)\) is an actual global lift there. The second
is not assumed Selmer there. Applying the twist differential identity
[Smith, eq. (3.1)](https://arxiv.org/pdf/1607.07860) to this global
lift and using the unmodified dihedral quartic high bit for the
now reversed cup gives the actual local corrected cocycles on
\(E_D^{tu}\). No untwisted second Selmer pairing is used.

On B and at infinity the local quadratic twist is trivial, so choose
the transported honest rational Kummer lift; both terms vanish.
At all unlisted odd good places the division fibers and corrections
are unramified. At the two c primes the normalized second class is
trivial. At the two b primes it has inertia \(T_0\) (bits 011);
the actual transported rational \(\kappa_4(T_0)\) reduces there to
the unramified \(\kappa_2(Q_0)\), for a rational half \(Q_0\) of
\(T_0\) on the untwisted model. Pointwise, take a geometric fourth
preimage \(R\), so \(2R=Q_0\); trivial local \(\kappa_2(T_0)\) and
rational full 2-torsion make all such halves rational. Pairing
the unramified Kummer cocycle against ramified \(T_0\) gives the
Legendre symbol of \(x(Q_0)\), its first coordinate. Duplication
gives \(x(Q_0)=\pm u/c_2\), and \(-1\) is square at both places.
This term has product +: explicitly use the Hilbert reciprocity
product for \((u/c_2,b)\), which is 1 at every prime of B (where b
is a square), at real infinity (b positive), and at every other
odd place not dividing b (both entries units). The support premise
includes literal rational denominators by the original definition
of B (scale numerator and denominator and root coefficients).

Thus only the quartic high-bit correction supplies the sign:
the product of the four rational quartic symbols of 2399, two
from b and two from c. The literal Euler exponents are −1 at
9807649 and +1 at 6469193. The exact rigid Gaussian ray fixes each
clone's Artin value: the relative cyclic quartic conductor at 2399
is tame exponent one, and its dyadic conductor divides the relative
polynomial discriminant ideal, bounded by the \(2^8\) part
of \(256\cdot2399^3\), contained in the fixed original ray. At these
primes the Artin value is order at most two, so a conjugate ray choice
does not invert anything material. Hence the rigid choice has
absolute sign + (pairing zero); the changed norm-one local residue
has absolute sign −. The latter cannot have a global point on
either of the stated covers, independently of conventions on
exceptional fibers: it would give a rational point on the actual
two-positive-factor [2]-cover and force a trivial Cassels value.

## Simultaneous supported tests on all five quotients

The four odd sign flips of a literal smooth pair cover are four
fixed-point involutions differing by the four distinct translations
in its 2-torsion deck. With any geometric origin their parameters
are a coset of \(E[2]\), whose sum is four times any one parameter.
The degree-two fibers over the selected rational conic points
therefore have sum equivalent to two hyperplane sections, because
twice each fiber is the pullback of a tangent. Equality of divisor
classes descends to a rational principal function here by Hilbert 90.
So the product of the four tangent sections divided by a fourth
power is a rational constant times a square. On a global product
against the same rational test argument that constant vanishes by
Hilbert reciprocity. A local point on the shared \(C_3\) can avoid
the finite zero sets without changing its existence, since it is
smooth at every local point.

I checked each ordinary [Shukla–Stoll (3.10)](https://arxiv.org/pdf/2302.01640)
tangent identity on this same local point:
the two ab/ac U terms cancel the common \(L_a\); the inverted
U product differs from the cubic one by \(L_aL_c\); the inverted
V product differs from the cubic one by \(L_bL_c\). The last two
come from replacing the two weighted difference tangents by their
direct difference and original-conic partners, each time over
the actual same installed quotient. Thus exactly the three specified
remaining nontrivial supported bits are enough after the positive
pair and the already fully pointed \(E_{ab}\) mark.

The three normalized governing cups have their stated second
character \(\chi_a\). At \(p_a\) its inertia is nonzero, while
the additional fixed characters from \(u-s,u,b(u-t)\) are
unramified. The commutator removes the first cup's repeated
\(\chi_a\), giving those three characters exactly. At the split
\(p_b\) over \(\mathbf Q(i)\), \(u\) is square there but is
globally nonsquare, \(u-s\) has nonsquare unit sign, and
\(b(u-t)\) has odd valuation. These provide independence over
the Gaussian field including the possible rational sign ambiguity.
The same commutator subgroup is central in the governing pieces,
fixes the order field at the stripped \(p_a\), and is invisible
to the abelian fixed quartic positive-root layer. Thus attach
all three chosen values after selecting the actual rigid zero
branch, if desired, with unchanged old ray/order restrictions and
tail. Each governing field ramifies only in the existing already
pinned support; no new distribution assertion is required.

**Scope:** the absolute failing branch is identified, and there
also exists a single choice passing all computed coefficient-supported
tests. The latter does not place the other four marked classes
in their full radicals, prove any rational point or give numerical
clone primes, arbitrary local approximation, or Lean compilation.

Signed: independent reviewer /root/high_review_ci.
