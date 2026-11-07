# Independent review: actual elliptic torsion

Accepted. Exact copied sources were independently rebuilt with `debug.skipKernelTC=false`; all 41 declarations in the two target modules were recursively audited. Only propext, Classical.choice and Quot.sound occur. The frozen upstream receipt and source hashes were verified, with no edits to upstream files.

The constructed map is into the actual Mathlib elliptic point group, not an abstract group supplied by a hypothesis. Integer multiples of a lattice period divided by N descend through the actual ZMod additive lift because N maps to a genuine lattice point, hence zero. The two chosen lattice basis elements are explicitly tau and 1. The parametrization sends (m,n) to the previously proved genuine point at (m*tau+n)/N, with the correct ordering of coordinates.

Injectivity uses the actual lattice-basis injectivity to turn lattice membership into the two integer divisibilities. Surjectivity uses actual Weierstrass parametrization surjectivity and its already proved addition law: if N*P=0, a complex preimage z has N*z in the actual lattice and is therefore the image of an explicit residue pair. The additive equivalence targets exactly the kernel of actual multiplication by N. The N-squared cardinality follows from that equivalence, not from a cardinality premise.

The order formula uses the lcm of the two residue orders and correctly simplifies to N/gcd(N,gcd(m.val,n.val)). The exact-order criterion includes N=1 correctly: the sole zero residue vector is primitive under this gcd definition, and the identity has additive order one. N=0 is explicitly excluded by NeZero N. The final primitive subtype equivalence is genuinely surjective onto every actual point of exact order N.

The accepted scope is complex elliptic points, their group and finite torsion sets. A relative torsion scheme, finite etale modular family, Weil pairing and source moduli interpretation are not claimed. Compatibility with modular coordinate transport is a separate live packet. This review uses the frozen upstream genuine torus/point producers; it does not claim independent re-proving of every imported analytic theorem.
