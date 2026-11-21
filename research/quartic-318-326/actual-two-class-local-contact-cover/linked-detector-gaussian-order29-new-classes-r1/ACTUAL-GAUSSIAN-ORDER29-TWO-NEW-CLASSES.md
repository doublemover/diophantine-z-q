# A 160-bit Gaussian divisor produces two different untouched detector contacts

Keep the literal J, four original Lucas labels and three scales, and
the complete shared CRT of the fourteen-contact certificate.
The following two new primes hit two different previously untouched
root classes, neither at the old root −1 nor at the recent −1/2 class.

| New prime | Literal slot | Root θ | Primary root of 2 | Full primary / opposite R orders |
| ---: | ---: | ---: | ---: | --- |
| 415721 | 241 | −32/407 | 10923 | 103693 / 29 |
| 9807649 | 292 | 1/2399 | 8296152 | 2453441 / 29 |

## A compact exact critical-index divisor

Use the already checked quotient of E:y²=x³−(3−rho)²x by T0,
with rho²=2:

    E′ : Y²=X³+(44−24 rho)X,
    P=φ(R)=(24−16 rho,−160+116 rho).

In the field Q(rho,i), i²=−1, the pointed automorphism
I(X,Y)=(−X,iY) has square [−1]. Its Gaussian multipliers satisfy

    ([5]+[2]I)([5]−[2]I)=[29].

The checker computes the affine x coordinate of Q=([5]+[2]I)P
by exact field operations in the basis 1,rho,i,rho*i. Its least
positive rational coefficient denominator is D_29², where

    D_29 = 996479897881955092985794918173310653967408040161
         = 953·19793·415721·567569·6469193·9807649·18415993·191616641.

All factors are verified prime by trial division. The rational
coefficient denominator of ([5]−[2]I)P is identical by i-conjugation.
For odd p≡1 mod8, the four signed specializations of rho,i are
unramified split and the basis-to-embeddings matrix has determinant
a p-unit (a scaled 4×4 Hadamard matrix). Thus p divides this
denominator iff the x coordinate has a pole at at least one such
place, equivalently that signed Gaussian multiple reduces to O.
This does not require expanding the much larger integer multiple
[29]P.

For p>76176 with p≡1 mod8, p≠1 mod29, this is exhaustive for
**opposite quotient order 29 in either arm**. Indeed nontrivial
29-torsion in E′(F_p) is then one dimensional: if it were two
dimensional the Weil pairing would give a primitive 29th root
of unity in F_p. The F_p-defined I acts on that line by one
of the two roots of −1, so 5+2I or 5−2I kills our reduced P.
This gives the stated denominator condition. Conversely at a
denominator prime either signed multiple kills P in an arm,
and their product is [29]. Since actual P stays a finite
affine point at good p, that quotient order is exactly 29.
This proof does not exclude p=1 mod29 or p=7 mod8 at integer
order 29; both complete-splitting/rank hypotheses are essential
to the claimed exhaustive list.

The exact six candidates above threshold have both literal order
and midpoint rows checked in the replay. Testing the weak
ord(2R) and opposite order modulo T0 for compatibility with the
entire old progression leaves exactly 415721, 6469193 and 9807649
on this scoped candidate list. Both selected candidates have
opposite *full* order 29, so no new sufficient T0-translate
argument is needed. 6469193 is not used for a contact here.

## Exact shared t,h

At each selected p, exact p² lifted point orders, first formal
returns, and Lucas evaluations give all four literal U charts
and all three scale residues. The twelve scaled nonzero root
classes are distinct mod p and the coefficient and root-minus-one
normalizers are units, putting both p outside B. Choose r/d
mod p² so T_j=c_j²(r/d)² is θ+p at its designated row. The root
square and Hensel computations give order-one contact there
and unit factors in the other two rows. Numerator CRT keeps
the full old fourteen residues. This gives the named tests
at symbolic d=B^N and arbitrarily large primitive r; the
recorded d=204 is a modular replay only.

Keep the old common index congruence and impose primary zero,
opposite one, and h=p³ mod p^4 at both new p. Both opposite
congruences are the **same** 29 congruence already present in
the fourteen modulus. The exact new arithmetic and real check
give at the passing h

    N(U([h]R)) in [−1059640787916845915,−1059640787916845914] / 2^64 (49152-bit directed dyadics).

with absolute norm >1/100. The old finite scalar rows and modulo
5 guards are retained, not the exact old scalar. The witnesses
are full-order ones, hence the existing pointwise sixteen-leaf
and signed trace-unit proof gives v_p(b_j)=+1 at both new
indices and all fourteen prior named incidences, at this same h,t.

## Support scope

Each newly hit class has one nominated prime and that prime
is a nonsquare at 7; symbolic denominator saturation requires
another odd-support prime in its own class. The three old −1 classes, one −1/2 class, and these two new
ones give six hit classes. All six
other nonzero classes still have the old triad's nonsquare
witness. Combining with the earlier independent character
conditions gives at least **28** odd-support primes in any
completion retaining these sixteen exact contacts on the
same saturated square branch: sixteen known, one more in
each of six hit classes, one in each of six unhit classes.
This does not imply that any of those remaining primes
individually exist with compatible orders or that the reasons
for insufficiency are exhausted.

Replay:
    python3 -B check_gaussian_order29_new_classes.py | cmp - EXACT-GAUSSIAN-ORDER29-NEW-CLASSES.json
    sha256sum -c SHA256SUMS

No claim about all order-29 primes across the excluded
congruence classes, complete support, square pole denominators,
a PointPair, or Lean.
