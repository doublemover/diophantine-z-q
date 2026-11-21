# Transvection tests realize all row directions for a finite candidate space

Use the actual G=GL₂(F13), Weil module V⊂M and simple quotient
Q=M/V from the
[exact image test](../actual-one-I-incidence-selmer-r1/EXACT-TRANSVECTION-IMAGE-TEST-FOR-ACTUAL-SEL13.md).
For any finite-dimensional subspace A of the ambient global
lambda Kummer classes, set A0=A∩H¹(ℚ,V) in the proven Weil
embedding and m=dim(A/A0). A transvection-prime test vanishes
on A0. Here a test is evaluated in the single nonfixed
degree-13 point completion, on the residue powerclass,
using any fixed orientation of its one-dimensional target.

## Joint distribution

Choose m representatives z_i of a basis of A/A0 as actual
Galois cocycles in M. Join their finite affine extensions.
On the splitting field of V their joint image is a
G-stable subspace W⊂M^m. Its projection to Q^m is
surjective. If it were proper, the simple modules in the
direct sum Q^m make it semisimple as a module, so a nonzero
G-map Q^m→Q would annihilate the smaller submodule.
Absolute irreducibility of Q follows by the same distinct
weights and unipotent proof over the algebraic closure;
hence each such G-map is an F13 linear combination of the
coordinate projections. Its vanishing would make the
corresponding nonzero linear combination of z_i trivial
upon restriction to the splitting field with values in Q.
It would therefore inflate from H¹(G,Q)=0, contrary to
independence in A/A0.

Fix one transvection u and one lift in the joint affine
group. All lifts are obtained by W. The operator N_u
on M has image a line supported on the nonfixed cycle,
kills V, and induces a surjection from Q onto that line.
Consequently as the lifts vary their simultaneous
13th-power values on the nonfixed cycle fill every
test row in F13^m equally often: the changes are
the surjective linear map from W onto m copies
of that line. Conjugating preserves projective row
direction and the zero row. Changing the chosen
nonfixed point or the residue Weil-root generator
multiplies the entire test row by a nonzero scalar,
so it has the same property. Chebotarev now gives,
relative to all good transvection primes:

    zero row:                         13^(−m),
    each specified nonzero direction: 12·13^(−m).

For m=0 only the zero test occurs. For a single
false candidate m=1, the test fails on exactly 12/13
of the transvection primes. The absolute failure
density is 1/169: the transvection conjugacy class
has 168 elements in a group of order 26208.
The script verifies these two finite constants directly.

It follows that for this particular finite space A there
exist m distinct rational prime tests whose rows determine
A0 exactly; fewer than m cannot do so using scalar rows.
These are existence and density statements about the
actual finite affine extension attached to A. They do
not exhibit a prime cutoff, guarantee independent outcomes
in a short prime range, or supply a certified basis or
dimension of the ambient class eigenspace for this d.
Finite tests can be used as upper-bound rows once those
arithmetic inputs are provided.

    sha256sum -c SHA256SUMS
    python3 -B check_transvection_counts.py | cmp - EXACT-TRANSVECTION-COUNTS.json
