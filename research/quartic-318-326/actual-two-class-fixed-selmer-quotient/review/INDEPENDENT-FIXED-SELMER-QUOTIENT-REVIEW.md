# Independent review: exact fixed Selmer quotient of the two-class cover

**Verdict: passes mathematics and bounded finite-witness review.**
This binds the source SHA-256
`864eda3ef9d3228456d21589d4f438ad5ed2cd8688c70d463862b237d0f974ae`
and manifest
`92707c5caff6f4f725ea91a068b1af621d67b423cf230569b5c83ed6f0ee118f`.
I verified the author manifest and replayed the known-support rows
byte-for-byte. This is a fixed exact system with some unresolved
literal coefficient prime factors, not a computed total Selmer rank.

**The quotient and its kernel are exact.** The pilot chart residues
in the archived XVI data give c_i² w_(p_i)² − θ_i = p_i
modulo (p_i^2) for both targeted pilots, independently of the stored
trace coefficient. This forces each within-pair Legendre symbol to
be +1. The two opposite support products are squares in all four
relevant completions; reciprocity therefore makes all cross bits
equal, and the checked pilot cross symbol is +1. At each moving
prime the three rational torsion rows and the identity have distinct
valuation vectors, exhausting the four-element local Kummer image.
At the a pair all their unit signs are +1; at the b pair only the
first two signs can be −1 and they equal ((-1)^{v_t}).
The exact q_i ≡ p_i (mod 8B) clones make the collapsed
classes indistinguishable at every fixed prime of (B). The twist
(D=ab) is a local square there, and the ordinary square scaling
preserves literal Kummer coordinates. The local requirements at the
moving primes reduce to the stated conditions on (x), any even
Ā, and C̄ ∈ {000,110}. Sending a vector to
(Ā,C̄) is surjective onto the actual fixed-place
system (M): choose one (A)-summand zero, and take the b-pair
summands with common third parity prescribed by the first static
Legendre bit. In the kernel both exponent pairs coincide,
with an arbitrary even vector on the a pair and one b-bit.
This is exactly (W), of dimension three. The two rational
torsion classes project to their actual untwisted torsion rows.

**Exact local image checks.** For integral roots at an odd place
with one collision pair, away from the node the two adjacent
classes agree and the separate class is square. In the node disc,
the separate sign is the fixed split/nonsplit sign; for nonsplit
it forces both adjacent depths to be at least the root distance.
Their minimum is that distance and the product forces equal
parities, giving exactly the stated even-depth unit and odd-depth
pair rules. The derivative specialization at a root obeys the
same conditions. These are exact because each allowed image has
four possible vectors, the actual local quotient size. At the
three odd exceptional coefficient primes the distinct torsion
parities prove equality directly. The dyadic calculation uses
(U=2y/(x^2+d^2)), whose numerator and denominator valuations at
(R) are respectively 5/2 and 1. The immutable author source swaps
“numerator” and “denominator” in this sentence; the displayed valuation
3/2 and subsequent argument use the correct quotient. The formal doubling
parameter keeps depth (3/2) under each odd label and gives
η ≡ 1 (mod 64). Two independent torsion vectors and
the exact test abscissa (S_0+640), with class ((10,10,1)),
give all eight local triples with third coordinate square.
The real middle coordinate is positive. Unknown normalized
(m,n,P) support must still be tested; split even-depth
places can contribute, so an odd squarefree support list is
not sufficient.

**Scope.** The computed sixteen rows form a four-dimensional
relaxation on the displayed known-support slice, not a
four-dimensional full quotient or a lower bound of four on it.
No full Sel₄ image, rational point, explicit moving primes, or
Lean compilation is claimed.

Reviewed and signed: **Vesper, independent mathematics review**,
2026-11-21 UTC.
