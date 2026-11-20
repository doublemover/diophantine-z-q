# Exact level-48 theta coefficient for the even genus partner

For positive squarefree D ≡ 13 (mod 24), the level-48 paper derives
the primitive-period normalized central value of E_(−D) from the
signed integral coefficient A(D): it is A(D)²/32. The two programs
implement the exact four-class quaternion packet and bounded lattice
coefficient examples. The reference D=146965 yields A(D)=256 and
recovers the previously certified central value 2048.

See the [formula and provenance](LEVEL48-POSITIVE-DISCRIMINANT-EVEN-COEFFICIENT.md)
and the [primitive-period certificate for the reference datum](../heegner-f53-fixed-example/high-hom-1120/heegner-odd-residue-example/EXACT-EVEN-CENTRAL-LATTICE-455.md).
The prose calls the latter by the staging filename ending
"-DISPLAY"; the linked archived filename contains the same reviewed
rendered bytes. Both programs use only Python's standard library and
integer arithmetic.

From this directory:

    python even48_brandt.py > /tmp/even48-brandt.json
    cmp /tmp/even48-brandt.json EVEN48-BRANDT-PACKET.json
    python even48_coefficient.py 13 37 61 85 109 133 157 181 205 229 253 277 301 325 146965 > /tmp/even48-control.json
    cmp /tmp/even48-control.json EVEN48-COEFFICIENTS-CONTROL.json
    python check_even48.py
    sha256sum -c SHA256SUMS

See the [independent cold check](INDEPENDENT-EVEN48-REVIEW.md).

D=325 is intentionally a nonfundamental program control only.
This is the even genus partner, not the separate odd mod-13
Heegner detector. The bounded evaluator has not been run at a
selected 68-digit twist and is not intended to be practical there.
There is no new linked-pole witness or universal rank claim.

The separate [binary norm note](SAME-THETA-BINARY-NORM-CERTIFICATE.md)
gives a criterion for full support splitting in a prime-discriminant
imaginary field and explains why finite local checks alone do not
settle an actual prepared scalar. Its minimum-scalar notation is
explained in [the accompanying arithmetic note](MINIMUM-SCALAR-GENUS-COMPATIBILITY.md).
The named bounded candidate JSONs are kept here with their original
integer-only generators.
