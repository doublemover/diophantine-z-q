# Actual signed local factors to the exact conditional global client

Green evidence: strict run 44827477142, artifact 14675761196, ZIP
6b4c3926e573411651390aef0a027c7f7d3389eaedb4f001f26908cb721656fb,
42/42 compiled and 561 declarations audited. Its exact 42 files remain
byte-identical. The 43/0 source-only first target adds only the logic of
specializing Cassels' equation to these exact signed local factors.
It does not ask to check the 1,190-owner legacy arithmetic graph.

## Exact remaining proposition

For positive squarefree n with (n : ZMod 12) = 11 put q=(n:ℚ) and
hnq=Nat.cast_ne_zero.mpr hn.ne'. The unchanged contract is

    ClassicalCasselsAt n hn hr =
      (nativeFullSelmerQ₂Finite q hnq ∧
        (-1 : ℤ)^nativeFullSelmerCorank q hnq =
          supportProduct (actualLocalSystem n hn hr))

The exact terminal proof passes hC.2 to the cheap 43-file theorem, and
passes the already-written native corank-zero lemma for its Finite case.
The hypothesis hC is not produced. The finite-dimensionality conjunct is
deliberately retained in the contract; the narrow contradiction needs
only the equation. No new oracle is defined.

### Existing donors and their boundaries

* **Green arithmetic/geometric right side.** OriginalCasselsLiteralIsogenyPoint318
  has literal_affine, literal_zero, literal_kernel_point, literalKernelEquiv
  and supplied_map_eq_literal. OriginalCasselsLiteralIsogenyAddition318.literal_addition
  builds the true additive point map for every field in its stated scope
  (in particular ℚ, ℝ and ℚₚ). OriginalCasselsActualLocalSystem318.actualLocalSystem
  fixes those exact lifts and actual quotients, not scalar inputs.
  OriginalCasselsActualSignedProduct318 gives selected_actual_support
  and selected_actual_product. This pins the match of the literal coordinates
  x+2n−3n²/x, y+3n²y/x², including O and (0,0), with the paper's
  a=2n, b=−3n² isogeny, partner a'=-4n, b'=16n². The support is the
  real place, 2, 3 and the distinct primes dividing n. It is not a
  root-number computation.
* **Source-only identification of the left-side object.**
  ActualTwoDescentActualHigherSelmer318.actualHigherSelmer uses actual
  continuous 2^k-torsion cohomology and genuine Kummer local images,
  at ℝ and every ℚₚ. ActualTwoDescentHigherLocalConditions318.
  actual_higher_local_condition_iff compares with the full local H¹
  kernel. ActualTwoDescentActualSelmerDirectLimit318.
  actualPrimarySelmerLimitEquiv gives the native additive equivalence
  from the directed system to the actual full primary group. Higher
  Kummer and PrimarySelmerShaExactSequence give literal rational Kummer
  quotient and Sha maps, not a global Euler characteristic.
* **Source-only comparison of duals, not parity.**
  ActualTwoDescentPontryaginRationalCharacters318.
  nativeRationalCharacterEquiv and ActualTwoDescentPontryaginPadicModule318.
  actual_native_character_scalar give the genuine discrete-Selmer compact
  circle characters, identified with dyadic rational characters and
  p-adic precomposition. DyadicPrueferModel defines the 2-primary subgroup
  of ℚ/ℤ; this is identified classically with ℚ₂/ℤ₂ via ℤ[1/2]/ℤ, since
  each x ∈ ℚ₂ has a dyadic rational fractional part. To use a theorem
  explicitly formulated with the latter as a native type, one needs
  the corresponding additive/ℤ₂-linear quotient comparison, not a
  different Selmer group. ActualTwoIsogenyParityInterface318 specifies
  the exact rationalization and native_corank_zero_of_finite, using
  FiniteModuleRationalization318.subsingleton_tensor_of_finite. None
  of these alone prove nativeFullSelmerQ₂Finite for all selected n.
* **Green, separate conditional CT lane.** The passed 30-owner
  CTOriginalDyadicReducedDescent318 cohort proves algebraic specialization
  *from* actual alternating pairing and maximal divisible radical. Its
  exact continuous Sha kernel and 2∞ quotient do not supply the genuine
  pairing, arithmetic nondegeneracy, isogeny adjointness, or a global
  Greenberg–Wiles formula. Raw continuous cup data, the H³ primitive
  boundary, isolated local invariant calculations, and conditional ABHN
  comparisons are not producers of this Cassels equation.

### First genuinely global comparison

[Dokchitser–Dokchitser, Root numbers and parity, §5 Thm 5.2](https://arxiv.org/pdf/0906.1815#page=11)
is the exact applicable unconditional prime-degree isogeny formula, for
K=ℚ, p=2; §1 fixes full rationalized Selmer corank. There is no
finiteness-of-Sha premise. Theorem 5.7 supplies this literal isogeny model.
This is a theorem available in mathematics, not an axiom or declaration
furnished by the pinned Lean library.

One can formalize this direct specialization, or rebuild the theorem
from narrower ingredients. In the latter route the first genuinely
global arithmetic step is the Selmer ratio for the two actual finite
isogeny local Kummer conditions (equivalently their exact global
localization/annihilator and Euler characteristic):

    #Sel_φ(E/ℚ) / #Sel_φ̂(E'/ℚ)
      = (#E(ℚ)[φ] / #E'(ℚ)[φ̂]) *
        ∏_v #coker(φ_v) / #ker(φ_v).

This is not the local product already proved. A rebuild must define both
isogeny Selmer complexes and prove the same local condition duality
(including real Tate convention), global restricted-product duality
and its cardinal ratio. It must then compare the global finite ratio
with the actual rationalized dual, carrying the dual-isogeny maps
and finite reduced Sha terms by compatible alternating pairings
(or prove the equivalent direct parity comparison). No exact
appropriate producer of these results was found in the project or
the pinned Mathlib tree; the nearby standard owners supply general
cohomology/Hilbert 90, Pontryagin dual, and rank-free squareclass
Selmer support. A finite-level Kummer exact sequence or an individual
Sha radical adapter by itself supplies neither global step.
See also [Klagsbrun, The distribution of the Tamagawa ratio, Thm 2.4](https://intlpress.com/site/pub/files/_fulltext/journals/mrl/2012/0019/0005/MRL-19-5-A14-KLA.dvi)
and [Lemke Oliver–Shnidman–Thorne, Elements of prime order, Eq. (2.1)](https://www.cambridge.org/core/journals/forum-of-mathematics-sigma/article/elements-of-prime-order-in-tateshafarevich-groups-of-abelian-varieties-over-mathbb-q/5591E877ABEDBB1D56F0A5D1986074AF).

The genuinely new global input is therefore ClassicalCasselsAt, or
a published-standard Lean theorem with these exact geometric and
cohomological specializations. Even if supplied, selected Selmer
infinitude/corank is not a Mordell–Weil point or the selected rank
conversion. Nothing here is a producer of the 2-converse rank-one RC.
