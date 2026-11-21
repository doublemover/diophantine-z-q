# Independent exact review: the original scalar mod-3 phase Hecke receiver

**PASS (paper and exact finite replay).** This review binds the
author checksum list
`799f583e1e4c1b8323d84a6ea77101b85dce1066a08910a33481dd9e53faf711`
and paper
`1c7366935cee10f6061f5886a5a2094ef54c05c975f72a04c10d3bf81bbe6523`.
All author bytes rehashed. The included exact script independently
reproduced the complete 96- and 144-label degree-five neighbor output,
including six cyclic kernels per label, multiplicity, symmetry, and the
literal phase eigenvalue modulo 3.

The level-48 quotient induces the conductor-48 Hecke eigenmap on the
Jacobian by multiplicity one. The pointed divisor comparison subtracts
the same rational cusp on each Hecke neighbor and specialization is at a
good residue prime, retaining the full 16 and 3 flags. The actual
operators negate the phase under Frobenius and the 3-arm, and preserve
it under the 16-arm; the latter swaps the two 2-eigenvalue flags without
losing the full stable cyclic subgroup. With both arms included, and
the odd Lie character and signed 3-flag both retained, all eight
subcontributions have the stated same scaled phase. The factor
eight times the chosen Lie character is a unit modulo 3.

I checked the primary
[Kane–Kim coset transformation and coefficient convention](https://link.springer.com/article/10.1007/s00029-025-01110-0),
Proposition 2.3, equation (2.10), and Theorem 2.5. The bilinear
normalization is the one with diagonal quadratic form Q, whose
determinant is a positive rational square by the local valuations.
The local level denominators are bounded by 8, 3, and the residue
prime. With the full marked congruence shift this gives the stated
common upper level. The inverse label multiplier in (2.10) yields
the positive character argument after reindexing the weighted sum.
Cuspidality follows from the 3-arm discriminant-module isometry
fixing the zero coset and commuting with the Weil transforms.

The actual prime-to-level correspondence reverses under dualizing.
For a fixed integral pulled-back trace-zero endomorphism, its index-p
superlattice test requires the diagonal coordinate divisible by p
and one off-diagonal coordinate by p squared. A norm divisible by
p squared gives exactly one good kernel in the nondivisible case,
the Legendre eigenline count in the once-divided case, and p+1
in the twice-divided case. The weights of the divided vectors give
exactly the character in the middle term and its square in the
last term. This recovers the full good-prime square-index recurrence,
not a rule for replacing a squarefree primitive coefficient.

No detector input, primitive Fourier coefficient, simultaneous
nonvanishing, rational point, or rank is supplied by this receipt.
The finite replay is a check of exact receiver maps, not a CM orbit
enumeration or a Lean build.

Signed: independent paper and exact-byte reviewer, 2026-11-21.
