# Independent exact review: residual Frobenius classes in the actual Gaussian prime selector

**PASS for the paper scope.** This review binds the author checksum list
`aac2afe2cc3cec0c32fce06750f06d8caedaa579a032c5ccef42c9802a4e610a`,
paper `ea90bce7537583e70e801f5a434538c219ea90f20242dcf62c8dc85528b8bef2`,
checker `aeb0f68a6248cd78b79bbd4508ee741e5abb1c2992b9dc415e456c753d4310e5`,
and exact checker output
`77723adb6125e298fa9000a7f742bf3e129cefb7b1cac228424ee6cd2bfa4d78`.
All files rehashed and the checker output reproduced byte-for-byte.
I independently recovered the published original Gaussian counting argument
with SHA-256 `29e5419420d73d1699801548e411527e265378ebd22bde95d7f7653d59fbc3e0`.

At 3, the literal base is split multiplicative with `v_3(q)=2`, so
after adjoining `mu_3` the Tate parameter still has valuation prime to 3
and inertia over that cyclotomic extension has a nontrivial wild transvection.
The irreducible Frobenius polynomial modulo 3 at the good prime 7
excludes an invariant line. Conjugating the transvection gives both
unipotent subgroups, hence the determinant-one subgroup; the cyclotomic
determinant gives the full group. The determinant is its only quadratic
character. The abelianized quotient is therefore unchanged when adjoining
this residual field to the original Gaussian ray: the fields meet in
the quadratic cyclotomic field, and in the compositum commutators contain
the entire 24-element determinant-one kernel.

I checked the normalized main term against [Frei–Tinková v3, Theorem 1.4
and equations (1.10), (1.14), (1.15)](https://arxiv.org/html/2408.17441v3#S1.SS2).
At each fixed cutoff, the compositum is rational Galois and the desired
inverse-image subset stable under conjugation. It is a finite union of
conjugacy classes, so the theorem is applied and summed per class.
The abelian subfield and its conductor are unchanged, so the local
support of every density term is exactly unchanged. Its denominator
`[K(mu_q):Q]` increases by 24 while its numerator increases by the
selected determinant-one class size. This gives the exact joint scalar
factor, rather than assuming probabilistic independence. Equal prime
forms are merged before assigning classes. The fixed factor still leaves
the old `N^2/sqrt(s)` lower bound larger than the `O(N^2/s)` bad-neighbor
upper bound by selecting `s` before taking `N` large at that fixed `s`.
There is no claim of a uniform error term for a growing family of fields.

Finally, tracing the identity forces any mod-3 quadratic self-twist to be
trivial on the representation kernel. In the full image the determinant
twist fails when tested at a determinant-minus matrix of nonzero trace;
in the determinant-one image there is no character of order two. Hence a
nontrivial positive twist ratio has no residual identification even after
a common imaginary quadratic base change. Compare [Kriz–Li,
Theorem 2.9](https://arxiv.org/pdf/1606.03172) only for the residual
hypothesis; it is not a theorem about the finite inert-13/19 receiver.

This is local Frobenius class freedom on the genuine original Gaussian
prime forms. It supplies no actual normalized CM class sum, nonzero
coefficient, Selmer element, rational point, or rank conclusion.

Signed: independent paper and exact-byte reviewer, 2026-11-21.
