# Produce the actual canonical CM count by quartic Jacobi sums

## Historical and inherited boundaries

Read the actual two-reductions proof in quartics/quartic-318-326/docs/sources/quartic_v10.tex lines11138–11165. Its formalized opposite-twist/canonical-curve reduction and elementary substitute for the Gaussian-associate argument are preserved as233 byte-identical sources from forward-canonical-cm-count-r2. This successor supplies the missing actual finite-field producer rather than assuming a count, Frobenius integer, trace identity, norm pair or Gaussian association.

This is a source draft, not a claim of hosted Lean acceptance. The analytic simultaneous-prime theorem and global rational-point/Anchor producers remain separate.

## 1. Produce the quartic character

For a finite field F with4 dividing|F|−1, choose a generator g of Fˣ and send it to i via the pinned MulChar.ofRootOfUnity construction. Its exact specification identifies the value at g. The actual quadratic character is nontrivial in characteristic not2; if its value on g were1 it would be the trivial character by the generator equality criterion. Its dichotomy therefore makes that value−1. Equality on g proves psi²=chi and psi⁴=1 for the actual integer quadratic character mapped to complex numbers. No quartic character is left to the caller.

## 2. Compare the actual cubic trace with actual Jacobi sums

The equivalence x↦(x²,x) identifies the whole field with the disjoint union of square fibers, including zero. The already proved exact square-fiber cardinality gives, for every complex-valued g,

sum_x g(x²)=sum_t(1+chi(t))g(t).

Take g(t)=psi(t)chi(1−t). The left side is S(1), because psi(x²)=chi(x), chi(−1)=1 and x(1−x²)=−(x³−x). The right side is J(psi,chi)+J(psi⁻¹,chi), since psi³=psi⁻¹. All sums are over the original complete field, not nonzero elements with exceptional terms omitted. S(1)=#E−p−1 is the negative of the conventional Frobenius trace.

## 3. Produce integral Gaussian coordinates

At zero psi is zero. At every nonzero element psi is a fourth root of unity. Factoring z⁴−1 into(z−1)(z+1)(z−i)(z+i) gives actual integer Gaussian coordinates in each case. Integer Gaussian coordinates are closed under addition and multiplication. Every actual summand of J(psi,chi) therefore has such coordinates, and the finite sum constructs integers c,d with J=c+di. Coordinates are not supplied as hypotheses.

## 4. Produce the norm and trace from pinned primary theorems

The pinned jacobiSum_mul_jacobiSum_inv theorem requires all of psi, chi and psi*chi nontrivial and target characteristic different from source. Nontrivial chi is obtained from an actual quadratic nonsquare. If psi were trivial, so would its square chi be. If psi*chi were trivial, psi³=1 together with psi⁴=1 would make psi trivial. Characteristic is0 versus the positive prime p.

Complex conjugation of a finite-field multiplicative character is its inverse, by the pinned MulChar.star_apply' theorem. Conjugation of the actual Jacobi sum is therefore the inverse-character Jacobi sum, while chi is self-inverse. Applying the pinned norm identity gives J*conj(J)=|F|. Taking real parts using the constructed integer coordinates produces c²+d²=p. The actual trace identity gives S(1)=2c. No unnamed Frobenius object or trace comparison is assumed.

## 5. Derive the real-coordinate parity from the actual curve

Instantiate the existing literal good-reduction model at the square unit coefficient1. The actual affine two-torsion points(0,0) and(1,0) give distinct nonzero order-two classes in the same formal quotient. The explicitly enumerated four-element subgroup has cardinality4. Its index formula, followed by the exact quotient-to-residue-curve cardinality comparison, proves4 divides the literal count of y²=x³−x over ZMod p. This is the same point carrier in the trace formula. With p≡1 mod4 and count=p+1+2c, integer arithmetic forces c odd. It is not a caller-supplied Gaussian associate condition.

## 6. Return to every original position and final same index

The preserved elementary prime-norm uniqueness theorem compares(c,d) with the original signed Gaussian(a,b). The original ray makes b even, and the constructed c is odd, so the swapped-coordinate alternative is impossible. Thus c²=a² and S(1)²=4a². CanonicalJacobiNorm318.canonical_from_ray has only the original prime instance and signed Gaussian ray as inputs.

JacobiIndexPreparation318 constructs this result separately at every original Fin3×Fin5 position, including repeats. It feeds the old canonical-count consumer, which feeds the actual opposite counts, orientation choices, quarter-orders, original CRT moduli and same final h. The final theorem no longer takes OneCount, CMMatch, AllCanonicalCM, a trace identity or Gaussian norm-coordinate producer. The original threshold/Q choice precedes the prime data, and the final h follows it. Conditional rational point-pair consumers and all original fixed roots/margins remain unchanged.

## Primary sources and validation

Pinned Mathlib revision56a005855ea17e0b0958f73ec801ae140b0a1679. Read bodies of MulChar.ofRootOfUnity/spec/eq_iff/star_apply', quadraticChar_card_sqrts/isQuadratic/ne_one and jacobiSum_mul_jacobiSum_inv, not just their names. Their pinned source hashes and theorem locators are in JACOBI-PINNED-APIS.json.

Finite exact checks construct actual quartic characters and Gaussian Jacobi sums for51 prime fields, cover13831 values and square fibers, verify the norm/trace/parity chain and Gaussian norm matching. The p5 sign control gives S=2,count8, distinguishing conventional Frobenius sign. The tests are not universal proof or Lean compilation. All233 inherited sources remain byte-identical. A fresh independent source review and hosted Lean check are required.
