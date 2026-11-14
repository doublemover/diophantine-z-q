module
public import OriginalConstructedMetricSections318
public import FinitePlacePrincipalImage318
public section
noncomputable section
namespace OriginalCanonicalFiniteLattices318
open NumberField OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open OriginalExcludedPlaceData318 FinitePlacePrincipalLattice318
set_option maxHeartbeats 1000000
variable (c : Fin 4 → ℚˣ) (t : ℚ)
  (hn : ∀ j, RationalContactPoint318.parameters c t j≠0) (i : Fin 4)
  (B : ExcludedGenerators c t hn i)

/-- The assembled lattice uses precisely the already-constructed good
cotangent generator and the displayed excluded-place generator. -/
@[expose] def generator (v : FinitePlace (K c t)) : K c t :=
  if hv : v (denominator c:K c t)=1 then
    OriginalGoodPlaceCotangentNorms318.normalizer c t hn v hv i
  else B.generator ⟨v,hv⟩

theorem generator_ne (v : FinitePlace (K c t)) : generator c t hn i B v≠0 := by
  unfold generator
  split_ifs with hv
  · exact OriginalGoodPlaceCotangentNorms318.normalizer_ne c t hn v hv i
  · exact B.nonzero ⟨v,hv⟩

theorem norm_generator (v : FinitePlace (K c t)) :
    OriginalFiniteNormAssembly318.finiteNorm c t hn i B v=(v (generator c t hn i B v))⁻¹ := by
  unfold OriginalFiniteNormAssembly318.finiteNorm generator
  split_ifs <;> rfl

@[expose] def modelLattice (v : FinitePlace (K c t)) :
    Submodule (ActualFinitePlaceIntegers318.Integers v) (K c t) :=
  lattice v (generator c t hn i B v)

theorem modelLattice_good (v : FinitePlace (K c t))
    (hv : v (denominator c:K c t)=1) :
    modelLattice c t hn i B v=OriginalGoodCotangentLattice318.modelLattice c t hn v hv i := by
  unfold modelLattice generator
  rw [dif_pos hv]
  rfl

theorem modelLattice_bad (v : FinitePlace (K c t))
    (hv : v (denominator c:K c t)≠1) :
    modelLattice c t hn i B v=lattice v (B.generator ⟨v,hv⟩) := by
  unfold modelLattice generator
  rw [dif_neg hv]

/-- Both unchanged original J² section values lie in each assembled
integral lattice. This does not assign geometric provenance to bad places. -/
theorem original_sections_mem (v : FinitePlace (K c t)) (n : Fin 2) :
    (![ContactBicanonicalPointHeight318.a0 c t hn i,
      ContactBicanonicalPointHeight318.a1 c t hn i] n)∈modelLattice c t hn i B v := by
  apply (mem_iff_norm v _ (generator_ne c t hn i B v) _).mpr
  rw [←norm_generator c t hn i B v]
  exact OriginalFiniteNormAssembly318.original_bound c t hn i B v n
end OriginalCanonicalFiniteLattices318
