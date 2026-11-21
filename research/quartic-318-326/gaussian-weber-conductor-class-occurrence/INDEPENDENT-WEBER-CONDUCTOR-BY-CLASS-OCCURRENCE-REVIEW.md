# Independent review: the exact absolute Weber conductor

Signed: Vesper, independent mathematical reviewer, 2026-11-21. Disposition: PASS for the paper argument from the stated exact Weil-free input, not a native Lean result.

Exact author paper SHA-256 df38f786fd5285d7e251bcf5ff8f583c86fd883556696fdf3e5d56e16b52a871. The immutable author archive SHA-256 is 5d799289c484c866c54cb1d94256568910b63eba22899b710fd78461f17e8588. The exact author checksums and finite arithmetic replay passed.

I checked that W is the absolute Galois Weber field containing the original K=Q(i), not a real-only subfield, and that even M suffices for the norm congruence modulo 2M. The norm is well-defined there under all stated modulo-M changes, genuine Gaussian units and conjugation. The argument uses the exact previously established positive arithmetic Frobenius on the same chosen Gaussian place as an input.

If the actual cyclotomic field were not contained in W, an automorphism of their compositum fixing W but not that cyclotomic field would produce a fixed absolute conjugacy class. Qualitative [Frei–Tinková, (1.10)–(1.12)](https://arxiv.org/html/2408.17441v3#S1.SS2) at q=1 gives an ordinary prime outside the finite exclusions; every conjugate still fixes W and has the same cyclotomic restriction. Its split Gaussian class being the identity forces rational prime norm 1 modulo 2M, contradicting that restriction. This is not a quantitative claim over growing M and does not assume the conductor to invoke class occurrence.

The previously proved abelian degree is exactly the cyclotomic degree, so the inclusion is equality. The lcm and totient check rules out any smaller cyclotomic conductor when 4 divides 2M. Applying the same fixed-field class occurrence to an arbitrary relative class gives its exact cyclotomic exponent as its Gaussian norm modulo 2M, accounting for both conjugations. This is the precise residue tag used in the separate prime-counting coefficient. No Weil-pairing formalization or full native result is claimed, and no marked rational point or quartic conclusion follows.
