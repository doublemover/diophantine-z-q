# Exact prime-ideal construction

Use the same original K and its freshly reconstructed FULL native integer ring O, not a chosen suborder. The literal integral quadratic algebra R has theta squared=-210. For p dividing210, the map z↦re(z) mod p is a ring homomorphism: the extra product term -210*im(z)*im(w) vanishes modulo p. Integer constants give a surjective map to ZMod p.

The kernel criterion is p|re(z), from the native integer-cast criterion. Write re(z)=p*a. Then z=a*p+im(z)*theta, proving universal inclusion in the two-generator ideal. Conversely both p and theta map to zero. This yields exact kernel equality, not just equality of norms.

Compose this reduction with integerEquiv.symm to obtain a ring homomorphism on the actual full native O_K. Surjectivity is the composition of the two actual surjections. Its native quotient equivalence is the first isomorphism theorem for this exact ring homomorphism. The commutative square sends the original integer element z to re(z) mod p literally. The native ideal membership criterion is retained on every O_K element.

The native ideal norm is the cardinality of the quotient, so the actual quotient equivalence proves norm p. Nonzero p rules out the zero ideal, whose norm is zero in the native infinite integer ring. Primality is supplied by the native Dedekind theorem that an ideal with irreducible absolute norm is prime. Finally specialize p to the existing PELPrimeNormalizerData prime labels 2,3,5,7, retaining their exact order. These ideals live in the commutative integer ring of the original CM quadratic field; no equation with the old quaternionic right ideals is inferred.

The preceding Minkowski theorem bounds representatives of every class. This packet supplies the actual small prime ideals needed for the next class-group construction; it does not yet classify every bounded-norm ideal or identify classes. External class field theory remains entirely separate.
