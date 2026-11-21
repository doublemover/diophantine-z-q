# Independent review: exact Gaussian Weber reciprocity

**Verdict:** PASS for the exact paper construction and its finite replay, 2026-11-21.

## Exact inputs

- `EXACT-GAUSSIAN-WEBER-RECIPROCITY.md` (algebraic revision 2): `2c33a234949d5da65d498ab8d2b4a0262ae2899198a907971b59df0d910d545d`.
- `local_control.py`: `04ff1e81b41991af98ab619c5796cff484e3fe5c5c348dd70d9b5026e1b29bc1`.
- `CONTROL.txt`: `3003d6794d0afb7ddfba480643bc9a1f46688284bbcadc82c19f85db8cbdfe0b`.

The exact command `python3 -B local_control.py | cmp - CONTROL.txt` passed independently. The finite examples are controls, not a proof by sampling the arithmetic or the field.

## Substantive checks

- **Actual finite field and quotient.** For the curve y²=x³−x over Q(i), multiplication by a nonzero Gaussian integer has degree its norm by duality. In characteristic zero, the proper-subkernel choice for each Gaussian prime power gives exactly that prime-power annihilator. Gaussian CRT gives one module generator of the full N-torsion. Equality of x² on two points is precisely relation by one of the four global units; applying this first to the module generator gives the exact kernel on the Weber field. Rational complex conjugation acts by conjugating the scalar even if it does not fix the chosen generator, and splits the absolute group into the two claimed cosets.
- **Arithmetic rather than inverse or conjugate Frobenius.** At a chosen split ideal, its own generator π has zero differential after reduction at that ideal. In the special fibre [π][bar π]=[p] and duality still gives degree p. The map factors through the coordinate p-th power, followed by an actual reduced global unit. Prime-to-p torsion reduction transfers that same arithmetic action to the Weber field. At an inert ideal the F_{p²} arithmetic action is −[p], by the point-count cancellation x↦−x and Frobenius characteristic relation. Quotienting by units gives the stated generator class in each case. This identifies the contraction itself; a generator is, as always, only determined up to a global unit.
- **Surjectivity without distribution.** Every unit class already has an integral representative coprime to the modulus. All its Gaussian prime factors are away from the modulus, including away from 2 and 3, and the product of their Frobenius actions gives that unit class modulo global units. This constructs an automorphism for each class, not a prime for each automorphism.
- **Exact extra dyadic bit and conductor.** The Weil pairing of a torsion basis at level 2M is primitive, and its Galois character on relative scalars is the determinant a²+b². The global units have determinant one. The kernel of restriction to level M is represented by 1+M z and fixes the primitive root, since its norm is one modulo 2M. This really descends the level-2M cyclotomic field to the level-M Weber field. Independently, the unquotiented unit group at modulus 16 has size 128, its conjugation-fixed subgroup size 16, and its wide-norm kernel size 16. That kernel is the product of the size-eight ratio image and the coset supplied by i, which is not a ratio (that would force equal coordinate parities). At each odd split or inert squarefree factor the norm kernel already equals the ratio image. Taking the single global unit quotient and CRT therefore gives exactly the absolute commutator kernel. Complex conjugation supplies −1 and the relative norm image is the units congruent to 1 modulo 4. The abelian subfield is thus exactly Q(μ_{2M}); no proper divisor of 2M gives this cyclotomic field.
- **What this supplies.** This is a paper producer of the actual field, signed Frobenius tags, and maximal abelian conductor used with [Frei–Tinková, Theorem 1.4 and (1.14)](https://arxiv.org/html/2408.17441v3#S1.SS2). It does not replace that analytic theorem, assert a Lean build, or produce the final rational point, any elliptic rank, or an unconditional forward quartic implication.

*Signed: independent proof reviewer, 2026-11-21.*
