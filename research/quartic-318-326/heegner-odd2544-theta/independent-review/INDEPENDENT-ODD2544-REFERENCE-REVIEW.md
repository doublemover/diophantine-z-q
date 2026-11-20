# Cold review: fixed odd2544 reference coefficient units

Inputs: manuscript 757ac9d731b5ec15cb776ed8487347621f4adafce19356e6ac727e1a0172f507,
script be160ba3f07261dda8f10aaec5f2196cef00b7d94e89fdc4c040cba2d06e660b,
result 52d5e4caca1ce5b9e4004584732e859729cc375db6dd857536eb738e2f4137bf.
The entire stdlib coefficient computation replayed byte-identically. The
adjacent checker independently verifies the literal reference point reduction,
local type signs, quartic-field readings and the calibration constant.

## Canonical finite coefficient weights

The two actual ternary sums are on the same 416 marked Eichler classes
already checked in the q29 End receipt, not an unmarked Brandt vector.
The denominator 29 is a unit at 2,3,53 and all type-I primes. At j=0
the extra order-three automorphism has irreducible polynomial mod 2
and cannot preserve any primitive cyclic 16-line; elsewhere only ±1.
Thus every ST stabilizer denominator t_x is 1. The code enumerates the
entire E0-relative maximal lattice modulo scalars; for each element it
imposes both exact line-preserving congruences before using that marked
class. This equals the marked sublattice sum for every class, with no
implicit class averaging, division by two, or substitute coordinate.
The two binary coefficient bounds come from the exact inverse ternary
Gram diagonal. Rational basis reduction is unimodular, and checking
both integer roots of the remaining exact quadratic gives each vector
once.

In the original [Sirolli–Tornaría paper](https://arxiv.org/html/2107.04483),
§3 has R_x=x⁻¹Rx; §4 has the minus polar form (4.1), conjugate local
character (4.5), and the norm-character/conjugation formula (4.13).
A determinant-one frame at 2 and 3 carries the literal primitive marked
line to the first coordinate (complete its generator to determinant one).
At q29 the actual isogeny gives the backwards Tate-lattice factor of
determinant 29; the other components can be 1, including the division
place 53 after the prime-to-53 identification. Both l symbols at 29
are 1. Thus the adelic factor is as computed. For type I the exact
isolated isotropic line test and minus polarization agree with (4.1).
At 3 take diag(1,0) in the actual marked frame; the type-II quotient
of polar forms is the chosen eigenvalue minus the other. At 53 the
same quotient against ω is the ω coefficient of the residue of A+B F;
the discarded F term is in the maximal ideal. The odd quartic character
with 2↦i is used with its conjugate. The quadratic character there
would be even and is not a substitute.

For W16,W3,W53=(+,-,+) and gamma types (+;−,+,+) and (−;−,+,−),
§9 (9.1) holds; type II is at 3 for both and at 53 for the second only.
The two theta weight characters on the quaternionic Atkin–Lehner
generators both have signs (+,-,-), as required by §6 Lemma 6.7:
at 53 the local division action is minus the classical W53 sign.
Both target discriminants and both auxiliary discriminants are
fundamental, so the unit fractional ideals in §5 Prop. 5.1 incur no
coefficient factor. The product discriminant intentionally has square
factors 17² and 19²; Prop. 8.1 (hence final Theorem B and §9 ratio)
removes the preliminary coprime hypotheses and applies to these types.
This matters because the two exact reference target twists also serve
as the opposite auxiliary twists.

## Exact normalization and scope

The primitive real characteristic-zero quaternionic eigenvector can
be chosen to reduce to the SAME λ at a selected prime above 13, by
the previously audited one-dimensional residual simultaneous eigenline
and Deligne–Serre lift; no complex or other prime is substituted.
Since all coefficient maps are linear and integral at that prime,
the modular entries give the reductions of the corresponding
actual characteristic-zero reference coefficients, not their exact
characteristic-zero values.

The independent finite group calculation on the exact E−1, u²=22,
gives [224](21,31u)=[11](22,15u)=(34,33u); the latter generator has
order 13. The two reference sums have reductions 3 and the conjugate
pair 2,11 (i↦5,8). The product of squared absolute values reduces at
the SAME local place to 3²·2·11=3 mod 13. A simultaneous change of
the retained sign of the reference period does not affect its square
4, so the ratio calibration factor is 4/3=10 mod 13. The three
candidate coefficients are all required to be units; no assumption
that conjugation fixes the chosen prime and no replacement of the
quartic pair by the square of a single residue.

The prior [Cai–Shu–Tian reference ratio](https://arxiv.org/pdf/1408.1733#page=12)
is pinned to K=Q(√−455) and its exact compatible d-family. This is
the accepted scope of the calibrated formula. A new m needs a
separate same-test-vector varying-K compatibility proof; the phrase
“any compatible d,m” is not by itself a supply of one. Any additional
original CCL or multiplier comparison is outside this computation.
No production d coefficients, linked scalar witness, rank, or Lean
result is established here.
