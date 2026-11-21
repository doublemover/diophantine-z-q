# A full factor-free ideal relation for the ordinary mirror q53

Keep the same actual covector field F^c, integral
line generator B, Gaussian generator Z, and principal
element gamma=Z−G(B) from the
[partial reduction](../actual-one-I-q53-global-norm-r1/EXACT-PARTIAL-PRINCIPAL-REDUCTION-OF-MIRROR-Q53.md).
The exact norm has residual integer C of 2940 digits,
with no rational prime below 200000. This packet recovers
the entire ideal supported over C without factoring C.

## Exact relative polynomial, not a guessed global field model

Over the actual degree-14 line field K, the conjugates
of Z under relative dilation are Z_b, b∈F13^×.
For a compatible cyclotomic root z, the point-field
expression Z_b=W Y_(z^b)(u) is the same normalized
derivative formula as the exact norm replay. Since
Z_(-b)=−Z_b, define

    Q(Y) = product_(b=1)^6 (Y−Z_b²).

The coefficients belong to K and are integral, and
the relative degree-12 minpoly of Z is Q(Z²), using
the already established primitive orbit. The paired
Gauss labels b=1,…,6 are one representative of each sign.

To recover all six coefficients, multiply them by
B^i for i=0,…,13 and take trace to Q. Modulo the
split-cyclotomic primes compute these powers in the
degree-84 monic x quotient using the exact derivative
formula for Y_z. Newton traces in that quotient give
the absolute trace, divided by the actual relative
degree six over K. If zmax is the integer upper bound
on every |Z_b|, the j-th coefficient trace has
absolute value at most

    14·48^i·binom(6,j)·zmax^(2j).

Fifteen recorded split-cyclotomic primes suffice for
a centered CRT product exceeding twice every bound;
a fresh prime checks it. The power-basis trace
matrix of B is invertible. Solving it over Q gives
the exact degree-13 coefficient polynomials in B,
with all rational denominators archived. Their
evaluation Q(G(B)^2) is the relative norm of gamma.
The full rational norm in degree14 of this exact
element equals the previous signed 2988-digit norm,
an independent consistency check against the
degree-84 one-specialization calculation.

## The complete composite ideal over C

The collected coefficient denominators are units
modulo C. Monic Euclidean division over the whole
Z/C gives a degree-one common factor of the exact
line polynomial and Q(G(B)^2), with no nonunit pivot.
Thus there is a single archived residue B_C and the
matching Z_C=G(B_C). Both the derivative of the line
polynomial and the derivative with respect to Z of the
relative equation Q(Z²) are units at the chosen residue.
Both equations and both derivative gcds are checked.

For each rational p|C, these simple roots lift first
in the actual line field and then in F^c, since the
relative polynomial is exact and its denominators are
units there. This produces a degree-one prime of the
maximal order and, through the same compatible roots,
a surjective reduction homomorphism to Z/p^v_p(C).
It makes gamma vanish to at least that depth by the
given residue equation. The maximal-order ideal norm
of that prime power is p^v_p(C), exactly the full
p-part of the norm of gamma. Containment and equality
of local norm force equality of the principal p-divisor.
Equivalently the composite ideal I_C is the kernel of
the CRT-compatible map O_(F^c)→Z/C with the two
archived residues. This proof needs no squarefreeness
or primality of C and no claim that the full displayed
power-basis order is globally maximal.

Every supported p-prime now has residue degree one.
Its relative scalar stabilizer is trivial, because
a rational good-prime Frobenius fixes this individual
covector. Also C≡21 modulo 53 and C^4≡24, so C is not
a 13th power. At least one prime exponent is nonzero
modulo 13 on a free orbit. Hence eξ I_C is genuinely
nonzero as a divisor modulo 13; its class is unknown.

Combining the exact 3, 53 and 5303 coefficients gives
the completed faithful principal row

    eξ[q_53] + 4 eξ[q_3] + eξ[q_5303] + eξ[I_C] = 0
                       in (Cl(F^c)/13)_ξ.

This is a reduction to two explicit small ideals and
one completely specified large composite ideal, not
yet a reduction to a certified small generating base.
It does not bound the ordinary faithful class rank,
finite Selmer group, or rational rank.

    sha256sum -c SHA256SUMS
    python3 -B check_relative_mirror_polynomial.py | cmp - EXACT-RELATIVE-MIRROR-POLYNOMIAL-AND-COMPOSITE.json
