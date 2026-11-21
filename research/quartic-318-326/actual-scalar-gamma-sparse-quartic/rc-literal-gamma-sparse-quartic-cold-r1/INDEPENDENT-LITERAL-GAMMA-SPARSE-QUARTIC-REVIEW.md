# Independent review: exact sparse quartic for the original marked Gamma

Disposition: **PASS, identity and bounded exclusion only**.
Reviewed author manifest SHA-256
`8efdb6fa867b30b8845a59e1e96e29378cdcd2cab3c5321abe82a8ea5c57b245`,
manuscript
`2a41789aaebe49a5580a14e3d5a48d506c8ae9e45b2f0ce4160730aaf54870d4`,
source `ca710d5d09050b4bdc65203e11c11b5d9abdc4d140878d283b3c12ecde6ab534`,
and exact JSON `49a587a2602523f9a1ba14c3a1297de324e72da2de31b6fdf4a95d11f32edc7c`.
All five upstream SHA-256 entries in the author manifest also match.

* Recovered the rational inverse by the conic substitution
  `r=K/(Z+2H)`. Neither sign of H is lost. In the original curve maps
  the identities `q+1=5(1-x)^2/F` and
  `4q-1=5(3+x)(1+3x)/F`, with `x=beta*r^2`,
  check the sign and all denominators of W, not just its square.
  The restrictions exclude the finite roots and the two infinity
  possibilities over Q; the inverse provides nonzero original
  ordinates and the required original nonzero denominator.
* Checked the integer primitive representation and its reciprocity.
  The same squarefree beta is split as `g*e` by `g=gcd(M,beta)`;
  the binary polynomial loses exactly a factor of `g^2`.
  The reciprocal interchanges `(g,e,X,N)` with `(e,g,N,X)`
  and retains normalized height. Thus 128 divisor choices suffice.
* Independently enumerated the four roots at each of the four
  certified visible theta primes, then all 256 CRT residues.
  For height at most 4,218,366,392, the determinant of two admissible
  reconstruction vectors has absolute value less than the modulus
  35,589,230,039,008,870,789. The strict convergent criterion applies
  to every reduced positive candidate. Enumerating all eligible
  convergents, without stopping at the first small remainder,
  independently reproduced the complete prefix counts
  `6110,1538,610,372,191,109,49,22,12,7,5,3,2,0`.
* Repeated the twelve ordinary source evaluations using actual-curve
  baby-step/giant-step point annihilators and an independent
  right-to-left affine ladder; all finite chart pairs and the full
  W, c and delta residues agree. The thirteenth cut, p=7, uses the
  previously independently checked literal singular-arm evaluation
  c=1, delta=6 modulo 7. The author replay is byte-exact.

Thus a rational point of this same marked Gamma, if it exists,
must have normalized height strictly greater than 4,218,366,392
in the two reciprocal charts. This neither gives a point nor excludes
larger-height points or points on the general Kummer fibre. It does
not assume one unseen theta prime or certify any Selmer or rank claim.
No Lean run.

Signed: independent proof and source review, 2026-11-21.
