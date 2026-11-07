# Actual elliptic N-torsion and primitive period vectors

For every actual tau in the upper half-plane and every positive integer N, this packet constructs an additive equivalence from (ZMod N)² to the kernel of multiplication by N on the actual normalized Weierstrass elliptic curve.

The parametrization is explicit: (m,n) maps to the previously constructed actual point at (m tau+n)/N. Integer lifts are independent modulo N because the actual lattice periods map to zero. Injectivity uses the actual lattice basis, and surjectivity uses the already checked actual Weierstrass surjectivity and addition law. The subgroup has exactly N² elements.

The exact additive order is N/gcd(N,gcd(m.val,n.val)). Consequently primitive residue vectors, defined by this gcd being one, are in actual bijection with points of exact order N. No abstract torsion structure theorem, cardinality hypothesis or supplied point-label map is used.

## Boundary

This is an actual complex elliptic group and finite-point result. It does not construct a relative torsion scheme, a finite étale modular cover, a Weil pairing or the specified modular family. Modular coordinate transport is a separate packet.

## Replay

`bash run.sh` strictly rebuilds both modules and audits every declaration recursively. The only accepted axioms are propext, Classical.choice and Quot.sound.
