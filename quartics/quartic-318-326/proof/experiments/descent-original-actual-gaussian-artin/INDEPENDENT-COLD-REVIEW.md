# Actual Gaussian finite Artin input, and separate signed norm source

Static and mathematical review under original r5 and pinned Mathlib
56a005855ea17e0b0958f73ec801ae140b0a1679. No Lean, workflow or publication.

## Gaussian arithmetic

Exact archive descent-work-20261120/actual-ray-arithmetic-artin-r1-increment.tar.gz
SHA-256 c2c2e229c2508087fe7d69692fcaeff648d0c0026495a3238ac17b568ba882c5,
exact receipt 30f00b50eaadf5b9dead4fc5c2638accf2487cd99d45d15b29e0fb1f02fe4ef5.
Independent tar comparison, SHA256SUMS and finite script all reran:
59,038 actual principal-kernel membership comparisons, 82 exact inverses,
328 coherent unit orbit lifts, 4 inert negative controls.

- **Same quotient** (DegreeFromFrobenius 100d5399…/DegreeOneGenerator 2f9132f3…).
  If I is the genuine contraction, then all y in Z[i]/I satisfy y^p=y
  by surjectivity from the very same integral Gaussian ring. Primality makes
  this very quotient a domain, p is zero from hpI, and p prime implies
  CharP p. The nonzero polynomial X^p−X has degree p because p>1, and
  gives finiteness plus an upper bound; canonical ZMod p injects giving the
  matching lower bound. No trivial Frobenius is assumed on an unrelated
  residue field, and no extension cardinality is needed. Arithmetic Frobenius
  is tested outside its bad primes at later use, not assumed by this pure
  lemma or across p=2. Exact proof pattern is Mathlib Finite.Basic 3d73633f…
  L435–439; Roots 582ae654… L134–143; Ideal.Quotient.Basic 104af7d1… L83–95;
  CharP.Basic b40e2de3… L104; ZMod.Basic aa726b1c… L392–425. Prime-quotient data
  is preserved literally by ofCard/ofRationalPower construction.
- **Norm p on the principal generator.** Pinned PID c2092643… L90
  supplies span = I for its chosen generator π. Then π divides p and
  itself not a unit by properness. Since the actual residue field is ZMod p,
  i has a genuine rational residue representative a. If the cofactor
  p/π were a unit, p would divide i−a, which has imaginary coordinate 1,
  contradictory. Both Gaussian factors have NatAbs norm ≠1, their norms
  multiply to p², and the exact prime-square lemma (same shape as pinned
  GaussianInt c34edded… L243–255) makes Norm π equal p, not p². Positivity
  of the Gaussian norm tidies the NatAbs cast. This covers p=2 purely
  arithmetically as well. No unrelated representation p=a²+b² is selected.
  The exact integer contraction and the quotient units likewise use I itself.
- **One global unit in the right direction** (ResidueOrbit 827620be…).
  Norm-coprimality produces the literal inverse of the reduced Gaussian
  integer: multiply its conjugate by an integer Bézout inverse of the norm.
  QuotientGroup.Defs 6ec41ce6… L145–149 gives [x]=[y] iff x/y is in
  the subgroup, so h.symm supplies TARGET/SOURCE. It is an image of
  one global Gaussian unit e; e times the original source equals target.
  Quotient equality in the ring means eπ−t is a multiple of M, giving
  both coordinates modulo M. Int.ModEq 44a56c79… L106 wants t−eπ,
  so the code's negative multiples are correct. A concrete sign control:
  π=2+i, M=16, t=−1+2i uses +i, not −i. Gaussian unit norm one gives
  (1,0),(0,1),(−1,0),(0,−1) and the +i turn acts as (a,b)↦(−b,a),
  literally matching old rotate. Exact norm/conjugation API in Zsqrtd.Basic
  604b2149… L421–449 and L469–491; Units.mkOfMulEqOne in Units.Defs
  2c070bf6… L292–297. The conjugation branch switches both related pairs
  in the old normalize theorem, so neither inverse Artin nor a spuriously
  independent local choice is made.
- **Boundary** (ReciprocityBridge f5292802… and optional Handoff 952cef8e…).
  Caller still supplies the actual projected arithmetic p-power identity and
  literal ray-class equality, plus actual reference and unit in its orbit.
  The source derives the coordinate congruences, norm and ArtinDatum, not
  class-field reciprocity, and doesn't infer any of it from prime mass.
  A future proof outside the packet may need named public ofCard_ideal /
  ofRationalPower_ideal to rewrite across opaque constructor bodies (or
  private import-all when proving those identities); both constructor
  equalities are evident internally, no material mismatch in current
  interface. Optional Handoff invokes the old Realizes from packets for
  every prime its supplied selector admits, or the narrower prior physical
  window mask should be used. It isn't part of the small arithmetic canary.

No definite source blocker in the cold pass. Exact disposable standard
parser verified predecessor ConjugateLift 447770ad191e26619f3707cc297840b6ec00079523c0359fd12137446cce7ffd
and four selected arithmetic modules against the progress baseline, no aliases
and no baseline imports. First smoke DegreeOneGenerator 1/0, then
DegreeFromFrobenius 2/0; separately ResidueOrbit 2/0 with common same generator;
combined ReciprocityBridge 5/0 including the byte-identical public
Mathlib-only orientation module. Exact disposable intake ba80a9ca… was not
a publishable active-slot request. Tiny proof diagnostics, if needed,
are the literal quotient root bound and explicit coordinate simplification,
not changes in theorem scope.

## Separate old-place norm and finite support composition

Author's exact files and stock selection revalidated:
- Original-old-place-import-r1 1/0, intake
  d34f4274d4c38d4084dcdc5ce561929bbd51c1736d25decc115ad713ec6c5586,
  source ff87deed7b5d69a8f56b81b1fa03c3cdf425d0f66e26212cb8e3f5183b3ee596,
  selector 940fe4f2672838415b720893adc81a2e4e04efddbb7b91f6538dab277548b8c7.
  Diff from exact 8aca3ac2… is only private proof import
  Mathlib.Algebra.BigOperators.GroupWithZero.Action at `Finset.smul_sum`.
  No new mathematical assertion, original norm and signed h22 point formula
  unchanged.
- Original-global-signed-norm-support 3/0, intake
  a04aef9c9a697ebf513734094e05a9e7f128a3966f916b728ce2dd6259d4c9e3,
  terminal e5ab9da57636098bad175f747a625edea74a6e96b74046b47355bc45bfad892d,
  selector 7bbbce69b2c6111f0cdd2a2a129168110a6841d3ce11ec7e63e95b776796827e.
  Includes the exact r1 donor and gauge fcc626cb… .
  If N is the same unaveraged signed norm, the raw primitive is
  L(NQ−mW)+N(iT cPlus)−iT(Lm c₀)+iTν. Correct transpose sign for
  z=cor(b)+δν and b₀=δW+δ(iT c₀). The key torsion follows by applying
  [a] to the same NQ−mW and the actual marked norm equality; compatibility
  with N also kills N(iT cPlus), while iT's image contains exactly all
  a-killed points by its supplied onto and Mkill. No averaging or
  division by the index. At each actual g, the finite cocycle difference
  becomes the displayed δ after iT; injectivity gives the equality on
  original pulled-back vectors, and π surjective descends it to chosen Γ.
  Only the coefficient/torsion action is assumed supported. Actual
  non-torsion geometric action, actual CM fields and comparison cochain
  producers remain premises. The output is not any general global
  cohomological statement.
- Independent regression rerun: 1,966,080 finite evaluations and
  491,520 failures when comparison terms are discarded. Raw source
  nsmul/zsmul and delta expansion signs all agree; no definite static
  blocker. The 1/0 proof-import leaf is the safest first standalone host
  test if selected, with 3/0 composition independent of Gaussian/CT.
