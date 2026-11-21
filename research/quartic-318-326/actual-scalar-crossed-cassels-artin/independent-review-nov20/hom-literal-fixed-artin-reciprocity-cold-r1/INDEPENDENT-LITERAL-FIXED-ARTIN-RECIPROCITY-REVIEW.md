# Independent review: both literal crossed signs by fixed-field Artin reciprocity

**PASS for the exact conditional sign receiver.** Audited author manifest `edaf26c4a0465ef6a4a1ef53a2c353dc1f62e09bdc562541627328c50aaccbcc`, with paper digest `f1806da0faee531ae851041af730fe944a3c0d4bff8e2d3fd40250ece580e978`. The author hashes and exact standard-Python output reproduce byte for byte.

The two fixed norms of the sigma entries are verified integer identities. Outside the odd prime support of beta and the relevant s, the parity of their local valuations follows directly from primitiveness: at an inert prime dividing z, reduction via the residue norm would force both coefficients to vanish, and at a split prime at most one arm vanishes. Its valuation in the split case is precisely twice the valuation of z. At a good denominator prime, both gamma arms (or the sole inert arm) have the negative depth of c, so Hilbert contributions combine to the rational character of s by residue norm. At a good integral prime with odd delta depth, exactly the gamma-zero arm contributes. This is the literal orientation over the fixed field, not an arbitrary local sign.

I checked all fixed supports and derived the sign table independently, first recovering c modulo p² from the four pinned literal pairs c and delta/p, then constructing the root of beta on the gamma-zero arm modulo p². The rows are:

- First test: (+, +, +, −, −, +), product +.
- Second test: (−, −, +, +, +, −), product −.

The columns are 2, the whole fixed denominator K, 131, 6551, 2470991 and 16782959. Both gamma values at 2 are 5 modulo 8, giving the stated dyadic signs. All odd primes of s are in the exact beta or visible theta support. The remaining fixed 3, beta and real symbols are trivial by the same literal local and positivity guards. Reciprocity therefore trades the two exceptional denominator symbols for the two unseen theta Artin products with constants + and −, respectively.

If a named test is actually admitted, its local rational s-symbol is positive at each unseen theta prime. Then the two oriented Artin values agree. The corresponding assertion for the product only needs the product test to be admitted; the two individual tests need not be. This validates the alternative ideal-of-norm-U input under the appropriate admission hypothesis. The degree-eight extension is dihedral: it has a nontrivial conjugation action on its biquadratic subgroup, and the hidden sign lies on the center, beyond the maximal abelian subextension. It is therefore not implied just by rational splitting data. The auxiliary p=1186981 control is not an unseen theta prime.

This exact result does not evaluate the unseen support, either Artin product, either full admission norm, or rational solubility. Its nonadmitted formulas still use the literal oriented prime, not an arbitrary norm-U ideal.

**Signed:** independent review lane, 2026-11-21 UTC.
