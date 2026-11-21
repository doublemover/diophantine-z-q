# The strict Selmer test needs only the ordinary mirror class group

Keep the same actual d and faithful reflected character
ξ on the degree-168 covector field F^c from the
[mirror class pairing](../actual-one-I-mirror-ray-class-r1/EXACT-MIRROR-RAY-CLASS-UPPER-BOUND-CERTIFICATE.md).
Write Sel_str for the kernel of localization at 13 in
the actual Sel13(E_d/Q), and q_ell for the exact mirror
degree-13 prime selected by each good transvection test.
This addresses an upper bound without computing global
Kummer generators, or even the projected ray unit group.

For any finite list of these primes define the **ordinary**
projected class quotient

    C_tests = (Cl(F^c)/13)_ξ / span{e_ξ[q_ell]}.

There is an injection Sel_str → C_tests^* (linear dual,
using the exact Kummer pairing). A strict class is already
zero at 13 before restricting to the point field, hence its
reflected character is locally trivial at both mirror places
over 13. It is unramified everywhere else by the exact
good/bad local conditions. It comes from the ordinary
class group. At each transvection prime its residue test
vanishes by actual V-descent; in the mirror field this
annihilates exactly the specified projected prime class.
All the embeddings and the sign character are the same
as in the cited mirror pairing.

In fact if all good transvection primes are used,
the reflected ordinary quotient dual equals Sel_str.
For the converse an ordinary ξ-character is unramified
everywhere. Each mirror prime above 13 is fixed by the
relative cyclic group, so its unramified Frobenius
is invariant and is killed by the nontrivial character.
The reflected Kummer class is therefore zero at both
original 13-primes. Its vanishing at all transvection
primes gives global V-descent by the exact image criterion.
Zero at the formal original point prime yields the true
ordinary local condition. The evaluation of the actual
ordinary line at the other original 13-prime is injective:
it is the nonzero ψ line, distinct from the killed ψ²
extension line as in the exact local packet. Thus zero
at that second prime makes the local V-class itself zero.
This is exactly Sel_str; no rank assumption is used.

The ordinary local Selmer space at 13 has dimension one, so

    dim Sel13(E_d/Q) ≤ 1 + dim C_tests.

Therefore an independently certified upper bound
**dim C_tests ≤ 1** suffices to give total finite Selmer
dimension ≤2, then full corank one by the previously checked
odd parity and the good ordinary 13-converse. This conditional
certificate no longer needs any ramified mirror ray modulus,
a full Kummer generator basis, or exact saturation of a
surjective relation presentation once its upper bound is
already at most one.

## Practical boundary for one candidate computation

The ordinary class field is still the same degree-168 field
with 2641-digit discriminant. Generation is the issue:
even if one writes down any number of finite prime symbols,
none of the finite tests supplies a domain dimension by
itself. The exact all-prime quotient above identifies this
with the strict Selmer question, not with a computable
automatic vanishing argument.

For perspective only, **under GRH** the primary
[Grenié–Molteni Corollary 3.8](https://arxiv.org/pdf/1607.02430)
ordinary class-group generation bound is
4.01·(log |Disc(F^c)|)^2. Integer comparisons in the
checker put this below 149000000 for this actual field.
But the first possible rational transvection prime is
53 (ell≡1 mod13), and every test ideal has norm ell^13.
The actual first test ideal q_53 has norm 53^13,
more than 10^14 times that conditional ceiling. Thus
even using this small-norm factor-base theorem, the
test-prime class must be related to the generating base
by genuine ideal relations; it is not itself an enumerated
small factor-base generator. The unconditional standard
Minkowski norm bound has 1257 digits. Neither comparison
is a computational lower bound for advanced class methods,
and GRH is not used in the Selmer/ordinary-class theorem.

This packet does not certify ordinary projected ideal
generators, a rank bound, a rational point, or any
numerical cutoff for the transvection test list.

    sha256sum -c SHA256SUMS
    python3 -B check_ordinary_factor_base_gap.py | cmp - EXACT-ORDINARY-FACTOR-BASE-GAP.json
