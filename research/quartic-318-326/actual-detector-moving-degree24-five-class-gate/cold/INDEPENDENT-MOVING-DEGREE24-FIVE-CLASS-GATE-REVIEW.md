# Independent review: the moving degree-24 five-class gate

**Verdict: PASS, mathematical sufficiency only.** Reviewed the exact author
paper `ACTUAL-DETECTOR-MOVING-DEGREE24-FIVE-CLASS-GATE.md`, SHA-256
`5fe6315a914a7ac2fbb5dbdeb8681d01e51a18056b7896974bee666923e9f554`,
and author checksum list
`c85a2754c74c184e69d96582a4d590fcd28502bae1248f122629ec3c09d48aa6`.
The author checksum replay passed.

I verified the local 5-Kummer conditions at 2, 3, and 5, the bad odd
twist-prime inertia argument, and the base counts at 5 and 7. Irreducibility
and a Tate transvection give the full residual image. The relevant global
classes evaluate on a fixed nonzero covector to class-group characters,
unramified and split at the stated places. The generator is fixed by
covector eigenvalue 2: coefficient conjugation gives that value, not its
inverse. Testing the span of conjugate covectors on the full division
kernel, then using the central minus identity in inflation–restriction,
proves the injection; it is not a class-group identification.

The line and half-fields are fixed by the projective action and the
squared scalar character. At the actual twist prime 17 the base division
field is unramified and the twisting quadratic field ramifies. The
covector degree-24 field therefore has the asserted genuinely moving
quadratic step over the fixed half-field. Descending to the ordinary
projective class field instead loses the standard scalar character; this
is not a general algorithmic lower bound.

For the one selected companion, an eigenspace dimension at most one
would give 5-Selmer dimension at most two. The root number and
[Dokchitser–Dokchitser, Theorem 4.19](https://arxiv.org/pdf/math/0610290#page=26)
give odd 5-primary Selmer corank, hence one. In this good ordinary,
irreducible case, [Yan–Zhu v4, Theorem 5.11](https://arxiv.org/html/2412.20078v4)
then gives rank one. The whole rational quotient by 2 fills that
companion's exact selected Selmer eight and yields existence of the
ordered mark. This does not identify an arbitrary point with that mark.

No class-group dimension, Selmer bound, rank, companion point, numerical
source, or other pole was computed. No native Lean result is asserted.

**Signed:** Independent quartic reviewer, 2026-11-22 UTC.
