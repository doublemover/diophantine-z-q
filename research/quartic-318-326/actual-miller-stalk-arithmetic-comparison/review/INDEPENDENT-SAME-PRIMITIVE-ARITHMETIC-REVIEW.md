# Independent review: actual signed stalk arithmetic comparison

**Bounded cold PASS.** Reviewed the exact source receipt
`996fe0583c87c2b34bcb827c486b55a632c1e7ed9ab414b8ce8d6e0a8a045fcd`
with original paper `ce15e49c4de47764e69e17946e8ce06f00d64a5d37dbb83fc9801def1a9c59c3`
and the display-corrected paper
`5856fda156776a7585448c2ec2e7ff24b5c9b08b6aabdab458fb13be59095125`.
No source bytes were changed. The corrected copy explicitly uses the
standard carry at i+j at least d.

- The three exact module hashes are `18672281e539804941d57afbc68a72cfc38b1d2ce928a236a1aacc65464ffac4`
  (literal ordinary four-stalk coefficient),
  `2a69208ae9105107df3d82dac933261571d34aa2f7001bc3adea19671a545972`
  (action-twisted local and global scalar cups), and
  `3bf1d424818e30bc909dd14e1e81dddd049374861089c98e63728777ba32a0d4`
  (same primitive and local invariant profile). Their direct source flow
  is exact: evaluate at the original positive first point and moved
  negative second divisor, then use g and gh in degrees (1,1) and (2,1),
  respectively. `W.epsilon` and `S.cycles` are reused, not reselected.
  The standalone coefficient packet is source-only. The two arithmetic
  comparison modules have not been built as a single intake with it;
  the legacy `continuousFullCocycles` double owner is an explicit, real
  launch blocker. No Lean or hosted acceptance is inferred here.
- [Poonen–Stoll §12.2 and Proposition 34](https://math.mit.edu/~poonen/papers/sha.pdf#page=27)
  give exactly the lift sigma with m sigma = tau in A[m^2], local
  m Q_v = beta_v, and corrected cycle (sigma_v - dQ_v) cup tau'_v - epsilon_v.
  For the target choice use the actual phi sigma and phi Q_v. The
  established signed point composite is psi phi = [2], so by the paper
  morphism argument psi is the actual dual, not its negative. Given
  a lift U in E[2m] and V in E[m], with phi U in E'[m], choose U'
  above U under psi. Then 2m U' = m phi U = 0, so duality and the
  level identity give e_{2m}^E(U,V) = e_{2m}^{E'}(U',phi V)
  = e_m^{E'}(phi U,phi V). The same algebraic-closure coefficient
  and exactly the same epsilon give equal local H^2 classes all places.
  No ABHN step is required for this fixed-primitive equality. Its
  use for a changed primitive, or classical choice-independence, is a
  separate operation.
- [Milne CFT III §§1.7, 1.9, 2.1](https://jmilne.org/math/CourseNotes/CFT.pdf#page=109)
  computes the arithmetic-Frobenius positive unramified carry and
  identifies the absolute Brauer quotient by inflation, not merely
  its displayed finite windows. Normalize the real nonzero class to
  1/2. This is the arithmetic input, whereas the source endpoint
  `stalk_actual_invariant_total` matches any supplied I on identical
  corrected cycles. It does not furnish the absolute canonical
  invariant or identify a native Picard or Cassels–Tate theory.
- With the separate classical divisible-radical theorem and the actual
  finite reduced 2-primary groups T,T', the canonical elliptic
  polarizations from [O] give perfect alternating pairings. Adjointness
  and separation in T give ker(psi-bar) = (im phi-bar)^perp; finite
  character extension in T' then gives |ker(psi-bar)| |im(phi-bar)| = |T'|.
  Thus the annihilator index is exactly 1, and substituting
  |im(phi-bar)|=|T|/|ker(phi-bar)| gives signed defect
  v_2|T'| - v_2|T|, even because both finite alternating groups have
  square order. This needs neither finiteness of total Sha nor an
  assertion on its odd-primary part. It is not a rank or rational-point
  assertion and does not make the duality input a native theorem.

Signed: independent reviewer /root/high_review_ci. No Lean or remote action.
