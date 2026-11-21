# Independent review: a nonzero ramified Frobenius pair at fixed p_a

Exact author manifest
`ffa5c2e0e18de6faf513287012eca53f521838f1cb5bfe1bfe5fd98a189bb4fc`;
paper `cddf799ca6a56c520de2b4f42a7f7e4711efd0aa99fa01c8f944eb7b8c3ae9af`.
The author manifest verifies. This review is mathematical, not a
numerical evaluation of the newform or an enumeration of the CM orbit.

1. **The actual selected family is unbounded at one fixed mover.** The
   prior same-scale proof (70410179) fixes p_a and permits q_a and q_1
   to be chosen once before selecting q_2 in the tuned Artin class of
   Cassels triple (0,0,1). Smith's Theorem 3.2 constructs the adjusted
   cup governor with ramification only in the fixed support. The
   detached primes already require both Gaussian neighbour counts to
   be units. Then the two-tail proof, not just finite Chebotarev, applies
   as in the one-class source (30b5f14f, section 4): positive fixed
   density after the cutoff classes and Euler product, a reciprocal-square
   intermediate Brun–Titchmarsh tail, and o(X/log X) above X^(1/4).
   Increasing the lower bound on q_2 only removes finitely many choices.
   This keeps D=p_a q_a q_1 q_2, the same local contacts and Frobenius
   phases, and unbounded squarefree |Delta| at the fixed p=415721.

2. **Tame level survives inside the actual Gross lattice.** Independently
   checked (p-1) 630374400/12 = 21838270464000, exceeding even the sum
   of the holomorphic zero bound 105062272 and the coarse exceptional-j
   mark bounds. Hence a nonzero marked supersingular differential value
   exists (not identified or computed). For each selected discriminant,
   embed the maximal quadratic local order by multiplication at every
   split quaternion prime. At tame level primes the module preserves an
   actual prescribed line after changing basis: an eigensummand in the
   split ring, or the nilpotent ideal line in the ramified ring.
   At 2 the split diagonal order contains the image of the integer
   (1+sqrt(Delta))/2 itself. At p the ramified quadratic local field
   embeds in the division algebra with integral ring contained in
   its maximal order. The trace-zero vector is then in the literal
   (Z+2R) lattice; norm squarefreeness gives primitivity, and conversely
   an integral representing vector of odd norm embeds the maximal order
   via (1+v)/2, hence is optimal.

3. **The phase restriction uses the congruence theorem.** The ramified
   uniformizer lies in P outside P²=pR_p; its degree-p coefficient
   is constant modulo P². Conjugating by an actual local unit with
   Hodge tangent d multiplies that coefficient by d^(1-p). The
   residue tangent map of the maximal division order is onto
   F_{p²}^×, giving the entire nonzero norm fibre. On that fibre
   the trace or antitrace zero condition after multiplication by
   the nonzero marked scalar is one F_p line and admits at most
   two points. The selected unit congruence is an actual coset
   v_0+pL since L_p intersect pR_p is pL_p; it is unrestricted
   outside p. The shift Q_1=p²Q, h=v_0/p invokes the **congruence**
   version of [Duke–Schulze-Pillot](https://www.math.ucla.edu/~wdduke/preprints/lattice2.pdf):
   Theorem 2(ii) gives equal genus and spinor-genus mass outside
   finitely many exceptional squareclasses, Lemma 5(i) supplies the
   positive lower bound from the nonzero local densities, and
   Theorem 3(i) realizes the fixed coset for sufficiently large n.
   The square factor is 1, and the anisotropic finite valuation at
   p is constantly 1. Taking a finite union of exceptional classes
   and qualitative thresholds over all possible good cosets is
   legitimate, and each exceptional class meets squarefree n in at
   most one value. No effective threshold or choice of a numerical
   discriminant follows.

4. **The pair and the ramified-level signs are the original ones.**
   [Gross, Proposition 2.1](https://archive.mpim-bonn.mpg.de/id/eprint/3578/1/preprint_1985_30.pdf#page=73)
   applies to the height-one formal maximal-order module with
   prescribed ramified Lie type. Serre–Tate and étaleness extend the
   actual prime-to-p level without rechoosing its specialized line.
   No inert-only optimal-embedding corollary is used at this ramified
   prime. Independently checked (-2207/p)=+1, so arithmetic Frobenius
   paired with its actual transported tame mark contributes the trace
   of F_s c. Correcting split level orientations by Atkin–Lehner
   multiplies the entire pair by a common sign, without changing its
   nonvanishing. The three ramified-level classes have genus sign
   equal to the differential eigenvalue and give the same contribution,
   yielding factor 8. They and the p-class are independent: a
   proper nontrivial product of ramified ideals could not be principal
   (its generator squared would be a rational signed proper squarefree
   subproduct of the fundamental discriminant, using the units ±1).

**Scope.** For sufficiently large selected members at fixed p_a,
at least one actual first-order Frobenius pair remains nonzero after
the ramified-level symmetry. Other pairs may cancel it. No nominated
modular value, full jet, rational point, rank, or saturation of the
fixed p_a cell is proved.

Signed: independent reviewer, 2026-11-21 UTC.
