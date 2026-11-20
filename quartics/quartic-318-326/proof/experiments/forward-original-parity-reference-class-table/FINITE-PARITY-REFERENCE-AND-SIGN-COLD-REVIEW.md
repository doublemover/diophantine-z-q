# Exact small parity leaves and actual reference boundary

Static source read and exact arithmetic controls, no Lean, workflow or push.
Mathlib source pin 56a005855ea17e0b0958f73ec801ae140b0a1679. Original geometric
object paths in r5 under 558a130e12a461d9b380b44510d457f0d3d8a29d.

## Small 1/0 leaves

- Selected local sign: high-hom-1120/selected-root-sign-typed/
  original-selected-local-root-signs, source
  b571bd33364f6860c7f9560beb3f4e2e8bb2212b4c51721e3605361324272c8c,
  intake 9311a5ae65fa26e1cfd5f78f44c4ef5fdb9a55e6049896acf4eba690d3b9abb1,
  selector 637d80cc68cdb4ec130a751436cf4a41122f5cc3100dc30366d428e5f0374357.
  Actual n≡11 mod12 excludes p=2,3 and p=4 isn't prime. Squarefree
  prime-factor product is n, and map_prod multiplies the actual
  χ₄ over that finite support, giving χ₄(n)=−1. Pinned Squarefree
  58b9a1a6… L342, ZModChar aef4a5cd… L42/L93 and Legendre.Basic
  f88b8b92… L274 match exactly. The archimedean −1 and finite
  product −1 cancel, preserving both actual old local signs.
  n mod24 picks the same r∈{11,23} for n mod8 and mod3,
  with no extra selector. Local epsilon factor identity, invariance
  under the local twists and two reference global signs are explicit
  inputs. This doesn't manufacture those inputs; it combines them.
- Finite module tensor: high-hom-1120/selected-root-sign-typed/
  original-finite-module-rationalization, source
  4eaac3f1e3c92ddb60fb33cfd938a107cf6281b5f32b3c9893a2065e74340044,
  intake 91046a051a0fb9045e880bf098cf77bca6f4045eee600080c85ea2f0d07bb647,
  selector 5687ad0f11ea76c4983e8f24f44f221c640308b2aa03ed1819e9e6fd318c7c40.
  Each m of finite additive group has some positive k with k·m=0;
  divide K component q by k and move the same R scalar across the
  tensor. No flatness or PID of R is used or needed. Exact pin
  TensorProduct.Defs 9e066da4… L135–149 explicitly has the **two**
  branches (pure tensor, addition); only obsolete induction_on
  has a separate zero branch. L180–193 supplies R-balanced
  smul_tmul from standard scalar tower; NatInt 17dcfb78… L106–115
  supplies the R and K natural smul identification; the order lemmas
  are generated in OrderOfElement e3ba013b… L74/L981.
  The output only kills a finite module after characteristic-zero scalar
  extension, not the actual Selmer quotient or any arithmetic rank.

Both exact author intakes passed the stock parser. No definite blocker.

## Finite reference class table 1/0

Exact joined-work-20261120/parity-reference-table-r1/
OriginalParityReferenceClassTable318.lean:
daad5dd0e7e255aeee5808dbe2b2e5b41fab99fea26c0be291545432baff6630.
Stock temporary fixture checks 1 draft/0 baseline, with only Mathlib
Finset.Card and Fintype.Prod. This proves the finite Bit/Finset control,
not whether every actual completed elliptic class is enumerated.

Independent exact arithmetic replay replay_reference_bits.py
08cc7f67c1ce4424749141b43dbe64f5a504828d3cf7815ac24a0120ef5744d3.
Recover the local generating subgroup directly from the two torsion
marked pairs (n,1),(3,−n), plus the actual x=−76 / −85 pair only at 2.
For each of the 256 original signed pair words at BOTH n, verify
individual acceptance against independently built signed/valued
squareclass subgroups at all four places (2,048 comparisons). Verify
the exact rational points and nonzero square multipliers too. Counts:
real image sizes 2, odd places 4,4, dyadic 8; filtered
256→128→32→16→8 at each reference, with exactly
{1,3,n,3n}×{1,−n}. Independent 1,906 squarefree selected n through
25,000 confirm the χ₄ product and reference slot reindex.

The abstract proof of local completeness uses the actual odd
multiplication-by-two group index 4, dyadic index 8, and unramified
good-odd-place conditions to bound supports. At n=11 and 23,
3 is a square unit at p=n, and the second stripped unit is
(−1)^(v_n) times a square. At 3, the second sign −n is a
square and first classes range over all four. At 2, both valuation
bits vanish and the second odd unit is 1 or 5; the first goes
over all four. Exact numerical values by decide have not been
kernel-checked and could still need declaration-local resource
diagnosis; no speculative repair.

## Actual original objects (distinct, larger closures)

- OriginalParityReferencePoints318 source 411a7ffb… at
  joined-work-20261120/parity-reference-r1, 786/222 exact source graph.
  Cubic and finite coordinates are correct: (x+3n,x−n) gives
  (3,1) for 11 with 6,8 and (1,−23) for 23 with 299/48,73/48.
  The original torsion point at x=−69 multiplies by (3,−23),
  so the translated actual point at n=23 gives the same original
  (3,1) mark. This is an actual global Kummer image and hence
  genuine every-local membership. Original LiteralKummerClasses
  L27–30 provides the six nonzero/exact-square conditions; original
  missing def visibility is handled for point and retained beta
  by the exact two proof-only import-all edges.
- OriginalParityReferenceResidue318 source acbf5ae7… same
  folder, 664/222. Modulus reduction is in the right direction
  (n mod24) mod d=n mod d for d=8 or 3. Same
  r=n mod24 in both Hensel calls; nr equals 1 in both residue
  rings, and nz products and r≠0 legitimate division.
  Squaring the Hensel roots divided by r gives n/r, not rn.
  ActualTwoAdicSquare L12 and ThreeAdicTorsion L9 are exact donors.
  No definitive new blocker found.
- OriginalParityReferenceActualUpper318 old 49c542e4… has
  definite private-body problem at hbad.2.1: ordinary
  SignedAllBadRepresented isn't exposed. Fixed in an immutable
  separate joined-work-20261120/parity-reference-cardinality-r1
  source 7c4400d76b79ec865ae20bf0f2e1ea5b564f28a3d0d8a6bde4448082102baa45
  with exact sole import all ActualTwoDescentSignedAllBadNormalization318.
  There is no alteration to any arithmetic body. Option Empty has
  only none, so monomial is the unique n power. At the true 3-place
  after torsion normalization the positive second exponent must be
  zero by Jacobi (11 and 23 are both 2 mod3). This reconstructs
  B=(−n)^ε s² in the original, not normalized, pair.
  Numeric norm_num uses pinned LegendreSymbol extension
  1f6074dc… L371–382; original project public path reaches its
  import in ThreeSymbol. New actual upper is 830/222.
- Optional exact terminal OriginalParityReferenceSelmerEight318
  82e86cc5… above the preceding sources is 968/222 (planning counts).
  Its Bool product splits true before false in the exact
  Fintype.prod_bool L43, and the proof commutes factors to 3
  then n. The transport hNeg ▸ and he ▸ goes from the group products
  known in the subgroup to their equal right-side labels; no
  membership in another model. Injection uses rational valuations
  of two distinct primes then nontrivial negative class, not Python
  counts; surjection uses the actual n-specific upper theorem.
  No new definite terminal blocker found by the short read. The
  exact table is **not** a tiny drop-in proof of this actual result.
