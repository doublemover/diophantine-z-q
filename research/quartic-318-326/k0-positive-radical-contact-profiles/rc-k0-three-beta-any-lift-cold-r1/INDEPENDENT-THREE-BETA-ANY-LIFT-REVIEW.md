# Independent review: all full Selmer lifts of the specified first key

Reviewed exact `ct-original-k0-3beta-any-lift-r1/MANIFEST.json` SHA-256
`d9eedbaa3d80894f09331053470dea0c6329a15db901c5e4d5553d006ae1eb0c`
and `EXACT-ANY-LIFT-FOR-FIRST-KEY-THREE-BETA.md` SHA-256
`3421473b3cc17da5d1f96527ef1f8524f7b518026287ccdb21360a621e96ba4a`.
Author checksums, both exact upstream hashes and the finite replay all match.

**Verdict.** On the numerical Ready zero-direction Jacobian, the paper gives an if-and-only-if certificate for the existence of a **full** 2-Selmer partner with first key \(3\beta\), allowing its second coordinate to vary. This is more precise than local first-isogeny admission and strictly less restrictive than the earlier specified second coordinate \(-1\).

* The primitive norm \(C=X^2-3Y^2\) is the exact first-coordinate split test at all primes of \(C\), regardless of their depth. When it holds, the first coordinate there is square and the odd local image of size four fills all pairs with second and third coordinates equal. Every candidate partner is \((3\beta,-u,-3\beta u)\), where the only possible odd prime support of signed \(u\) is \(3\beta C\). At 2, at 3 and at \(\beta\)-primes the available variations are the exact local pure-second fibers, not heuristic unit conditions. At infinity both second signs occur for positive first.
* At an even-depth \(A\)-prime outside \(\beta\), the third slot is separate. Its Kummer parity is even; when the collision is split, its unit class is square and forces the corresponding \(u\)-test. At primes of \(B=A+3D^2\), the second slot is separate. The bit for \(-u\) must be square at split primes and at odd collision depth. At a nonsplit even-depth collision the entire unramified space is attained; in the odd-depth case, a nonsquare separate class would force an odd valuation in one of the clustered factors, so an all-unit triple instead lies on their equal-coordinate line.
* The two finite quadratic algebras are étale at their indicated odd moduli. In a split residue algebra a scalar must be square in the base, whereas every nonzero scalar becomes square in the inert quadratic residue extension. Hensel and CRT give precisely the required roots modulo the composite moduli, without factoring them to verify a certificate. The remaining odd \(B\)-exponent test is exactly that \(M=B/3\) is a norm from \(\mathbb Q(\sqrt{-u})\). At primes dividing \(u\) in \(\beta\), \(M\) is a square unit since \(M\equiv D^2\); at those in \(C\), \(M\equiv(4/3)D^2\), a square because the first split test was imposed. At 2 and 3 it is a square unit and at the real place \(M>0\). Hence there is no extra local obstruction to the norm conic; Hasse–Minkowski and clearing denominators give the exact ternary certificate.
* The \(D=115\) example genuinely has no Gaussian \(M\)-representation but admits \(u=829\). The two integer congruence/norm witnesses reproduce, and \((51/115)=-1\). Thus the marked bit can be nonzero for an alternate lift even when the earlier specific-lift test fails.

No key admission for the actual original scalar, no claim on other first keys, and no marked rational point, rank or full PointPair inferred. Independent mathematical/source cold review: high_review_ci. No Lean execution or remote operation.

