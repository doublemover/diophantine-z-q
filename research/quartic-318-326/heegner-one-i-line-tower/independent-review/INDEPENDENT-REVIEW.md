# Independent review: actual degree-14 line tower and field discriminants

Bound to author note SHA-256
\`d79bb98afba44d9afde6ed6995d51a4d0d159d2ed2ee1f750a6a68157109b4fb\`
and the citation-only successor
\`2dccbe27357c45e0909f0ba55f4fe09ef479b0892406cb49ad49e3a154a380fa\`.
The four replay sources/results are identical across these versions.
Both author commands reproduce the exact JSON bytes. The successor changes
only the citation in this note; the separate parity note is not covered.

The six affine x coordinates are the orbit modulo sign of the actual same
point under 2 mod 13. The 13-scaled coordinate is integral; their elementary
symmetric functions and sum are fixed by this six-element relative group.
Newton traces divide by the true relative degree six. The stated coefficient
and trace bounds suffice for centered CRT; a degree-14 squarefree character
polynomial forces the line sum to generate the actual line field. Trace
pairing then determines the exact coefficients in the same power basis,
and the final square equation is obtained by direct substitution. None of
these statements says the displayed order is maximal.

At 2 both prime-to-residue-characteristic torsions identify with those of
the same potential good special fiber for E_1. An automorphism acting
trivially on all torsion of order l=3 or 13 has degree of its difference
from identity at least l^2 unless zero, while the degree parallelogram
bounds it by 4. The projective scalar kernel is the shared central sign,
since the determinant on inertia is one. The 3-division quartic under the
stated affine change gives an Eisenstein generator and different exponent
4; hence transitive projective inertia cannot be V4 (its first wild term
would alone contribute 3). The A4 first wild term contributes 1 so consumes
the entire Swan exponent, yielding upper break 1/3. The line action has
three and five orbits under A4 and V4. The sign and vector actions have the
claimed free orbits. The determinant-one central extension is binary
tetrahedral, with Q8 before break 1/3 and a central remainder. For the
actual twist, -d is 5 mod 8 and defines an unramified quadratic twist of
E_{-1}; x=X+1 identifies that curve with 48.a4, whose conductor has
2-exponent 4 (https://www.lmfdb.org/EllipticCurve/Q/48/a/4). Its
two-dimensional Swan exponent 2 therefore forces total positive break
length 1 and central remainder 2/3. This reproduces the three 2-exponents
14, 98, 266.

At 13 the previously certified literal mod-169 calculation makes the
nonformal translated [13] equation Eisenstein after preparation. The
parameter t=-x/y is odd, so the additive-looking constant equation is
exactly the negative-point equation, not an approximation to formal
addition. Invariant differentiation makes its derivative 13 times a unit;
the Weierstrass-preparation unit does not change derivative valuation at
the root. This gives normalized different 13 over the unramified base.
Faithful residue action gives unramified descent to intermediate fields;
residue degrees 1, 6, 12 give nonformal exponents 13, 78, 156. The other
factor adds 0, 5, 11, giving totals 13, 83, 167. The tame split transvection
at 3 and the central twist inertia at each prime of d give the stated
remaining factors. Relative discriminant norms and digit estimates agree.

The first draft's linked article was Lorenzini, not Kraus. The successor's
Kraus potential-good reference and Cali--Kraus different paper correct
that pointer. This review establishes explicit field and local
discriminant input only, not class-group generation, a faithful eigenspace
rank bound, global independent scored elements, a Selmer dimension, or a
rational point.

Independent reviewer: Vesper (high_review_ci), 2026-11-21 UTC.
