# Independent review: pure-second Cassels neutrality and the literal scalar

Reviewed exact `ct-original-k0-pure-second-neutral-r1/MANIFEST.json`
`0156d15726e60eca8e3fd6d732ad7af4d7e16b4498f4fe08a811b2ea80161496` and theorem note
`a2d1700957ea3af4320e95e424bf3577d1236cf839ccb1a452bce1838c868310`.
Also reviewed `ct-actual-scalar-k0-supported-admission-r1/MANIFEST.json`
`969b47723c8b7982ec007c60910a9608a1ed15f1fa3f3d92f89f85c102db2e1d`
and theorem note `2dc3332aad79091dbf4ab2ec6ebd2acd2b3b25232c3858bc29cf5628ca444166`.
All author checksums passed; the scalar's full replay matched its archived output byte for byte and every scalar upstream hash matched.

**Pure-second verdict.** For any **actual** Selmer tuple \((1,d,d)\) on the literal zero-direction Jacobian for a numerical Ready pole, the normalized local product against the mark is \((2\beta,d)_v\). This identity includes signed \(d\) and unknown odd support. Hilbert reciprocity makes the global pairing trivial, so the mark's pairing functional factors through the first Kummer coordinate. This is not a claim that the full functional vanishes.

1. At 2 the square abscissa cuts \(d\) to the unit classes \(1,5\). The normalized infinity point has tangent product \(s^2(s+D)(s+2D)\) with \(s=D\sqrt{1-\mu}\); its class is \(14\) at \(v_2(\mu)=4\) and \(6\) at greater even depth, both equivalent to \(2\) for pairing with those \(d\)'s. At 3 the odd competing root depth cuts \(d\) to classes \(1,3\); choosing \(\sqrt{1-\mu}=1\bmod9\) gives class \(6\), pairing trivially against both, as does the square \(2\beta\).
2. At odd primes of \(\beta\), the two independent torsion parity patterns exhaust the local image; requiring the first coordinate square picks precisely \(1\) or \(-3\beta\) in the second. The unit tangent product gives \(6\) in the symbol, because \((\beta,-3\beta)_p=(3/p)\). At \(p\mid C\) the product is \(32A^3\bmod p\), of class \(2\), and \(\beta\) is a square unit. At \(p\mid A\) of even depth and at \(p\mid A+3D^2\) the second or third coordinate is the separated one, so \(d\) has even valuation. The primitive opposite-tangent argument handles all other good primes including \(p\mid D\). The chosen positive real product is harmless for either sign of \(d\).
3. Independently checked the scalar's original \(h,J\) and, by separate sequential addition in the two residue curves at 88079 rather than the author's binary step, obtained arm orders 3670 and 5505 and literal values \(H,I,f,N,Q,W=(78061,51599,31925,71812,13600,0)\). Since the literal normalizing factors are units, this gives positive even numerator depth without fixing its exact size or factoring it. The exact support enumeration has only one positive nontrivial candidate after 2/3, \(d=72485172522267769\), and the new split node forces its third coordinate square, which it is not. The strictly positive ten-prime-supported subspace on this exact scalar is therefore trivial. Separately, the universal pure-second result also neutralizes any other admitted \((1,d,d)\) on this scalar, whether signed or on outside support.

For a nonneutral Cassels partner on this scalar, its first coordinate must involve support outside \(\beta\) and the companion numerator \(C\): at companion places the separated first coordinate is square, and the eight old positive first-coordinate rows force the remaining \(\beta\)-supported first coordinate to be trivial. No existence of a partner, original PointPair, finished grid, or rank is inferred. Independent mathematical/source cold review: high_review_ci. No Lean execution or remote write.

