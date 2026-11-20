# Arithmetic Frobenius to one actual ArtinDatum

Source only. Four arithmetic leaves plus an optional existing-Realizes
receiver, no Lean build, CI action or push. This does NOT prove global
class-field reciprocity, define a virtual prime selector to assume the
answer, or redo the previous signed finite orientation realization.

## Exact external theorem boundary

Work with the actual Gaussian ring R=Z[i], positive fixed modulus
M=B*T and its ray class field K_M over Q(i). The conjugation-invariant
modulus makes K_M Galois over Q. At an unramified rational prime p
prime to M with ARITHMETIC Frobenius in the chosen conjugation-stable
set, fix a prime Q of K_M above p. Let I=Q intersect R, the actual
prime ideal above p. The selected Frobenius belongs to
Gal(K_M/Q(i)), i.e. its restriction is the identity. For every
z in R, the arithmetic congruence at Q therefore gives z^p=z
modulo Q, and contraction gives it modulo the SAME I. Also p is in I.
These are precisely hFix and hpI in artin_of_restricted_power.
There is no degree-one field given to that receiver, no assumption
of an unrelated representation p=a²+b², and no inverse Frobenius.
The separate source proves the residue size p from these data.

Now choose the positive residue reference r and a single conjugate
branch dictated by membership over the fixed base selector. The
remaining exact global assertion is a concrete equality in

    (R/(M))^× / im(R^×)

between the residue unit of a principal generator of I and the
unit for r or conjugate(r). This is the ray-class reciprocity
identification after restriction. Relative arithmetic Frobenius
uses p, not p², once the actual quotient size has been proved p.
The map from the residue quotient sends a residue to the ray class
of its PRINCIPAL IDEAL, using the arithmetic Frobenius convention.
Equality in that quotient is exactly the hClass argument, not an
arbitrary isomorphism between placeholder groups. Its proof still
needs the global field/Artin identification; no source axiom added.

Primary provenance: Kopp–Lagarias, [published
paper](https://msp.org/ent/2025/4-1/ent-v4-n1-p.pdf),
Essential Number Theory 4 (2025), 1–65, Theorems 1.1, 1.3, 6.5,
Corollary 6.7, Theorem 7.2 and the maximal-order specialization.
The all-integral p-th-power contraction uses the ordinary arithmetic
Frobenius at the chosen prime (relative to the rational base).
See original V13 exact manuscript lines 18992–19046 and the earlier
positive-reference orientation receipt. No general CFT theorem
admitted into Lean here.

## Deterministic native reductions (independently testable stages)

1. ActualGaussianDegreeFromFrobenius318 works with the actual quotient
   R/I, a domain since I is prime. Every point is a root of X^p−X
   by hFix and quotient surjectivity. This polynomial, p>1, has
   degree p and is nonzero. The finite-root bound gives finiteness and
   size <=p. On the other side, p is zero in the quotient and p is
   prime, hence the quotient has characteristic p and the canonical
   ring embedding ZMod p injects; size >=p. Equality is exact.
   This proves degree one from the real residue power relation.
   The negative control in Q(i) inert residue fields is i^p=−i, not i.
2. ActualGaussianDegreeOneGenerator318 accepts the residue-size
   equality via ZMod.ringEquivOfPrime and forms the actual Euclidean
   domain/PID generator pi of I. It identifies the integer contraction
   with (p) and proves modulus M avoids I from p coprime to M.
   To obtain Norm(pi)=p without a hidden determinant or norm theorem:
   pi divides p; since the quotient is degree one, some rational
   residue a represents i and i−a lies in I. If the cofactor of
   pi in p were a unit then p would divide pi and hence i−a,
   impossible because the imaginary coordinate of i−a is 1.
   Both factors in the Gaussian product of p are nonunits; their
   natural norms multiply to p², so each has norm p. This uses
   the same elementary prime-square lemma used by Mathlib's
   GaussianInt donor. No matrix determinant or algebra norm equality.
3. ActualGaussianResidueOrbit318 uses the literal principal-ideal
   quotient R/(M). From gcd(Norm(z),M)=1, Bézout gives an actual
   residue inverse for z: an integer inverse of the norm times
   conjugate(z). Thus the chosen principal generator reduces to a
   unit, with neither a unit assertion nor an inverse oracle assumed.
   In the actual group quotient the equality [source]=[target]
   implies target/source is the image of some ONE Gaussian unit e.
   Thus e*source=target, not the inverse direction. Equality in
   the ideal quotient means e*pi−r is a multiple of scalar M,
   so both integer coordinates are congruent modulo M. Gaussian
   norm one classifies e among the four quarter-turns.
4. ActualGaussianReciprocityBridge318 packages the concrete equality
   plus the same residue-ideal data. The terminal artin_of_restricted_power
   uses the restricted arithmetic Frobenius equality, not even a
   prior degree-one assertion, and outputs the unchanged ArtinDatum.
   A target unit belongs to the selected ray-group numerator; field-side
   Artin membership already provides it. No reference primality is
   assumed. ActualGaussianArtinDataHandoff318 optionally composes
   this with the already-written deterministic orientation module.
   If realized only on the genuine physical window, use the prior
   exact coprimality guard 2M<N<=2p; no artificial all-primes claim.

## Verification and dependencies

- Mathlib pin 56a005855ea17e0b0958f73ec801ae140b0a1679.
  GaussianInt blob c34edded…, PID c2092643…, ZMod.Basic aa726b1c…
  (ringEquivOfPrime, castHom_injective), QuotientGroup.Defs 6ec41ce6…
  via its exact eq_iff_div_mem source, Polynomial.Roots 582ae654… and
  FieldTheory.Finite.Basic 3d73633f… (degree/root-count donor patterns).
  The first three arithmetic leaves use only the pinned Mathlib and
  one of the local pure leaves; no original proof runner needed.
  The fourth imports only the old pure finite orientation leaf.
  Optional fifth imports original Realizes closure, not needed as
  a first independent check.
- Exact old pure orientation donor 447770ad191e26619f3707cc297840b6ec00079523c0359fd12137446cce7ffd
  from ca95531b…; old Realizes donor d4747d9da8f1c3b25c28388fe5d5b6f134e4886799bc4fa673ff55eb76afc5b5.
- Python controls compare actual evaluation kernels (a+bi→a+bt), where
  t=−Re(pi)/Im(pi) mod a fixed toy split p, against principal ideal
  membership via conjugate(pi) and norm p. They also verify inverse
  units, four-unit orbit multiplication and both real/imaginary
  congruences, plus four inert negative controls. No number field,
  analytic prime-pattern assumption or large search is implemented.
