# Exact abelian conductor and conjugacy orbit of the actual Gaussian selector

**Scope.** Original 318/326 ray field, pure finite source increments and
paper use of class-field theory. Independent cold field-count arithmetic
pass by the joined worker. No Lean build, CI dispatch, push, or formal
global ray class field construction; nonlinear prime lower untouched.

## Literal fields and sizes

Write K=Q(i), fixed B=2^e b with b odd and e≥4; B contains 7, 51,
the odd continuity support and all fixed coefficient/collision exceptions.
The core uses B=16 times the squarefree odd part if desired, since the
specified odd local conditions use only reductions mod primes.
For fixed selector cutoff s let T be the squarefree product of NEW
odd primes through s not in B (through the fixed preliminary exceptions).
Put M=B T, U_M=(Z[i]/M)^×, A_M=U_M/im{1,−1,i,−i}, K_M the full
Gaussian ray field with ideal modulus M Z[i]. The modulus is invariant
under conjugation, hence K_M/Q is Galois. Over Q(i) it has group A_M
by principality and the maximal-order ray exact sequence. Actual
complex conjugation lives in G_M, has order two, and projects
nontrivially to Gal(K/Q). Thus the sequence SPLITS with
G_M=A_M ⋊ {1,c}, c acts by Gaussian conjugation. One doesn't infer
a split extension from an arbitrary quotient of order two.

For M=2^e times the odd part m, |U_M| is

    2^(2e−1) product_{ell^j || m} ell^(2j−2)(ell−1)(ell−chi_−4(ell)).

At 2, units are the Gaussian pairs of opposite parity; at an odd
prime the split norm ring is F_ell×F_ell, the inert one F_(ell²).
For powers ell^j a residue is a unit iff its reduction is one,
and there are ell^(2j−2) lifts. The four global units inject mod16,
so [K_M:Q]=|U_M|/2≤M²/2, or in fixed-base form

    [K_M:Q]=2|A_B| product_{ell|T}(ell−1)(ell−chi_−4(ell))
            ≤2|A_B| T².

This is fixed before nonlinear sampling. It is not a claimed
field-uniform PNT or estimate of a varying field.

## Exact maximal abelian subfield: Q(zeta_(2M))

Let delta(z)=z/bar(z) in U_M. Its kernel consists of conjugation
fixed units. At odd ell^j, being fixed forces imaginary=0 and
the real coordinate is any scalar unit, giving phi(ell^j).
At 2^e, the imaginary coordinate is 0 or 2^(e−1), both even;
the real coordinate can be odd arbitrarily, giving 2^e in total.
Thus |Fix c on U_M|=2^e phi(m)=phi(2M).

The intersection delta(U_M) with the four global units is exactly
{1,−1}. The unit −1 is delta(i). If delta(z)=±i then at 2 the
equation z=±i bar(z) forces real and imaginary coordinates of the
same parity, impossible for a unit. This remains true at arbitrary
odd prime powers and arbitrary shared base ramification; it is
a dyadic obstruction, NOT an assumption of disjoint fields.
In the semidirect product the commutator is precisely the image
of delta on A_M: commutators with c give all these elements, and
the quotient by them has trivial action and is abelian. Hence

    |G_M| = |U_M|/2,   |G'_M| = |delta(U_M)|/2,
    |G_M^ab| = |Fix c on U_M| = phi(2M).

For inclusion, Q(zeta_(2M)) contains K and its arithmetic Artin
character on an ideal of K prime to M is its absolute ideal norm
modulo 2M. A principal ray element alpha=1+M beta locally at each
Gaussian prime above M has norm ≡1 mod the odd component of M.
At 2, beta is in Z_2[i], so Tr(beta)=2 Re(beta), and the exact norm
expansion 1+M Tr(beta)+M² Norm(beta) is 1 modulo 2M locally.
This handles fractional ray generators: the only reductions are
local, all denominators are units at the relevant primes, and
the positive rational ideal norm is reduced by its unit denominator.
The principal ray subgroup is therefore in the kernel of this
cyclotomic Artin map; the standard ray class correspondence gives
Q(zeta_(2M)) ⊆ K_M^ab. Since the degrees agree, equality holds.
Here 2M is divisible by 32, so the cyclotomic field's finite
conductor is exactly 2M (not the usual n≡2 mod4 exception).

Primary CFT source: Kopp–Lagarias, [published Essential Number Theory
article](https://msp.org/ent/2025/4-1/ent-v4-n1-p.pdf), Thms 1.1, 1.3,
6.5, 7.2 and Cor. 6.7, specialized to the maximal order.
The explicit 2M computation above is an independent inference
from those standard results and finite Gaussian arithmetic, not
stated as a theorem of that article.

Consequently the actual abelian residue F in the squarefree-W
transference can be taken to be 2M. Once W includes its prime
support, lcm(W,F)/W = 2^e product_{ell^j || b} ell^(j−1).
With the minimal allowed squarefree odd base and e=4 this is
literally E=16, independent of s after the support is included.
Also a≡9, b≡0 mod16 fixes the rational norm p≡17 mod32; at 7
the norm is 3, all other odd base primes norm 1. For higher base
powers determine the whole class mod 2B using the fixed reference
norm, not just these reductions.

## Exact orbit, local counts and optional inert field

Conjugating an element of A_M by (a,c^epsilon) in the semidirect
product sends it only to itself or its conjugate. For the chosen
positive reference r, (9,0) mod16 fixes the associate unit; after
that the two modulo-7 values (1,3) and (1,4) prove the two ray
classes are distinct. These are the actual two-element rational
conjugacy orbits of each admitted positive ray; full C_s is their
union. Unit normalization ties all primes to that same branch.
With CRT, once the base ray is fixed every new unit coordinate is
free before adjacent-norm constraints; no residual division by
4 or selector field degree.

For a split ell, in coordinates x,y the two adjacent factors are
(x−1)(y−1), (x+1)(y+1), so there are (ell−3)^2 admitted units in
total. On fixed norm d≠0 this count is ell−3 at d=±1 and ell−5
otherwise. At inert ell, total safe units ell²−3 (all units except
±1); on fixed norm d the count is ell−1 at d=1 and ell+1 otherwise.
Thus the exact total size of the full C_s is twice the product
of these total allowed unit counts. On each compatible abelian
d mod 2M, replace each total by its listed fibre count and use
the denominator |G'_M|=|G'_B| product_{ell|T}(ell−chi_−4(ell)).
The small split ell=5 generic zero fibre is a fixed base exception.
No assertion that this finite counting supplies genuine prime mass.

Optional smaller field: T=T_sp I, with I product of new inert
primes. Use K'=K_(B T_sp) Q(zeta_I), keeping exactly the split ray
information and requiring rational norm d≠1 mod each ell|I.
K_(B T_sp) and Q(zeta_I) are linearly disjoint since the former
is unramified at every ell|I, whereas inertia in the latter at
each such ell is the whole CRT ell factor. Both are Galois.
The commutator of the product is the split commutator times 1.
K' is inside the full K_M (both component inclusions by ray
monotonicity or the abelian subfield description), and

    [K':Q] = 2|A_B| product_{ell|T_sp}(ell−1)^2 phi(I),
    [K_M:K'] = product_{ell|I}(ell+1),
    K'^ab = Q(zeta_(2M)).

The norm selector at I preserves the two signed adjacent tests
on every generator, but is stronger than the original at d=1.
The same conditional lower-bound envelope still applies. If
feeding the old full-modulus ReciprocityPacket unchanged, use the
original field or take the preimage of the smaller Frobenius
condition in the full field; that preimage lies in the old
literal C_s because every inert angle is safe at d≠1.
A projected Frobenius element cannot on its own name a full
residue class; one may NOT pass it as the full packet class.

## Native leaves and controls

- ActualRayQuotientConjugation318 constructs conjugation on the ACTUAL
  Gaussian residue quotient ring, unit group and ray-unit GROUP
  QUOTIENT, proves its involution and proves exact cardinal two
  for the specified ray/conjugate pair.
- ActualIndexTwoRayOrbit318 is a separate Mathlib-only source:
  semidirect conjugation formula, exact two candidates, and
  crossed_commutator giving the a/bar(a) formula.
- ActualGaussianDoubleConductor318 supplies integer norm transport
  modulo 2M, the native dyadic no-±i-in-coboundary proof in the
  actual residue ring, −1 as coboundary, and exact norm mod 32.
- Source inputs from c2c2e229… actual Artin packet, ca95531b…
  pure finite orientation. No compiled native claim.
- Exhaustive finite controls on nine small even moduli check unit
  inverses, |U|/|delta|, exact image/kernel of norm modulo 2M,
  including arbitrary higher odd powers and unit intersection.
  Nine small fresh angular counts and the (9,0)/(1,3) mod16/mod7
  conjugate distinction also checked. No search for mainline primes.
