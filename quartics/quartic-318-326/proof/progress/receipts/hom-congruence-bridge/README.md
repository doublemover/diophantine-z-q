# Integral Hom-lattice congruence descent

## Checked result

`MatrixCongruence318.finite_order_eq_one` proves that any finite-order integral matrix whose actual reduction modulo 3 is the identity is the identity. This works for any finite matrix index type and does not require an externally supplied torsion-free-kernel theorem.

`HomLatticeDescent318.finite_image_representation_trivial` then proves:

- For a group G, an actual representation rho:G→GL(n,Z),
- a finite image of rho,
- and actual identity reduction mod3 for every rho(g),
- every rho(g) is the identity.

G itself may be infinite, as for the relevant Galois group.

## Proof

The first-order expansion `(1+x)^m=1+m*x+x^2*C` is proved inside a possibly noncommutative ring. For a prime-order matrix congruent to identity modulo `3^(k+1)`, cancellation of the common integral scalar improves the congruence by one power whenever the prime order differs from 3. The exceptional order 3 is handled by the exact cubic expansion

`(1+3dB)^3 = 1+9d(B+3(dB^2+d^2B^3))`.

Cancellation still gives that every entry of B is divisible by 3. Induction therefore makes every entry of A-I divisible by every power of 3; the integral valuation bound forces those entries to be zero. A general finite-order matrix is reduced to a prime-order power internally using `orderOf`.

## Exact source application and remaining boundary

V10 approximately lines 6982–6991 applies this to H=Hom(A,B) for two fiber abelian varieties over the degree-at-most-576 splitting field L. The standard arithmetic-geometric inputs are:

1. H is a finite free integral lattice.
2. Its Galois image is finite, since a finite basis of geometric morphisms is defined over a common finite normal extension.
3. A[3] and B[3] are defined over L. For every sigma, sigma(phi)-phi kills A[3], so it factors through [3] and belongs to 3H. Thus the actual integral action is identity modulo3.
4. Galois-invariant geometric morphisms descend to L.

Given a basis, the checked theorem makes this finite image trivial. The packet formalizes the matrix/congruence step and the finite-image representation consequence. It does not formalize the abelian Hom lattice, quotient-by-isogeny factorization, or geometric Galois descent; those remain the explicit source application, not hidden assumptions named as already proved.

## Build and audit

Topological module order:
1. MatrixCongruence318
2. MatrixThreeTorsion318
3. HomLatticeDescent318

Run `bash run.sh`. Fresh strict-kernel replay and an exhaustive recursive audit passed 26 declarations in these three modules. Only propext, Classical.choice and Quot.sound occur. Exact hashes and logs are retained. No repository/Git edits were made.
