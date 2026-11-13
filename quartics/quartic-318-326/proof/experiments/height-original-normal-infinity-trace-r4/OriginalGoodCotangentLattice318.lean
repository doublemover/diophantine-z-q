module
public import FinitePlacePrincipalLattice318
public section
noncomputable section
namespace OriginalGoodCotangentLattice318
open NumberField OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open OriginalGoodPlaceCotangentNorms318 FinitePlacePrincipalLattice318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0)
  (v : FinitePlace (K c t)) (hv : v (denominator c:K c t)=1) (i : Fin 4)

/-- The actual integral squared-cotangent lattice, expressed in the ORIGINAL
rational point's differential-square frame. Its generator is selected only
with a finite/infinity cotangent-comparison provenance certificate. -/
@[expose] def modelLattice : Submodule (V c t v) (K c t) :=
  lattice v (normalizer c t hn v hv i)

/-- Actual lattice membership is equivalent to the constructed local norm
bound. The integral ring and original rational frame are both retained. -/
theorem mem_iff_bound (x : K c t) : x∈modelLattice c t hn v hv i ↔
    v x*finiteNorm c t hn v hv i≤1 :=
  mem_iff_norm v _ (normalizer_ne c t hn v hv i) x

/-- Both literal original J² sections lie in the actual local lattice. -/
theorem original_sections_mem (n : Fin 2) :
    (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)∈modelLattice c t hn v hv i :=
  (mem_iff_bound c t hn v hv i _).mpr (original_bounds c t hn v hv i n)

@[expose] def integralFrame : V c t v ≃ₗ[V c t v] modelLattice c t hn v hv i :=
  basis v _ (normalizer_ne c t hn v hv i)
theorem integralFrame_value (a : V c t v) :
    (integralFrame c t hn v hv i a:K c t)=algebraMap (V c t v) (K c t) a*normalizer c t hn v hv i :=
  basis_value v _ _ a

/-- Every other primitive actual chart comparison gives the SAME embedded
lattice, not just an equal numerical height contribution. -/
theorem independent_of_generator (β : K c t) (hβ : β≠0)
    (hm : max (v (ContactBicanonicalPointHeight318.a0 c t hn i))
      (v (ContactBicanonicalPointHeight318.a1 c t hn i))=v β) :
    modelLattice c t hn v hv i=lattice v β :=
  eq_of_norm v _ β (normalizer_ne c t hn v hv i) hβ
    ((normalizer_max c t hn v hv i).symm.trans hm)

/-- At least one of the actual two original sections itself generates the
full lattice. The pair's primitivity is an integral-module statement. -/
theorem one_original_section_generates :
    modelLattice c t hn v hv i=lattice v (ContactBicanonicalPointHeight318.a0 c t hn i) ∨
    modelLattice c t hn v hv i=lattice v (ContactBicanonicalPointHeight318.a1 c t hn i) := by
  rcases le_total (v (ContactBicanonicalPointHeight318.a0 c t hn i))
      (v (ContactBicanonicalPointHeight318.a1 c t hn i)) with h|h
  · exact Or.inr (independent_of_generator c t hn v hv i _
      (OriginalGoodNormSupport318.second_value_ne c t hn i) (max_eq_right h))
  · exact Or.inl (independent_of_generator c t hn v hv i _
      (ContactBicanonicalPointHeight318.a0_ne c t hn i) (max_eq_left h))
end OriginalGoodCotangentLattice318
