module
public import OriginalArithmeticTensorFiber318
public import OriginalAllPlaceFrameCoherence318
public section
noncomputable section
namespace OriginalIntrinsicFiniteLattices318
open NumberField SectionHeight318 PELOriginalManuscriptNormalization318
open OriginalAllPlaceProducedNorms318 ActualFinitePlaceIntegers318
open OriginalArithmeticTensorFiber318
variable (c : Fin 4 → ℚˣ) (u v : ℤ)
  (hf : ∀ j : Fin 5,ContactRadical318.forms u v j≠0) (i : Fin 4)
  (w : FinitePlace (K c u v))
local notation "E" => OriginalArithmeticTensorFiber318.fiber c (t u v) (hn c u v hf) i
local notation "R" => Integers w
local instance : Module R E := Module.compHom E (algebraMap R (K c u v))
local instance : IsScalarTower R (K c u v) E := IsScalarTower.of_compHom ..

/-- Select the already constructed ACTUAL model/zoom differential
normalizer at this finite place; no new lattice or bound is assumed. -/
@[expose] def normalizer : K c u v :=
  if hw : w (ContactArithmeticDenominator318.denominator c:K c u v)=1 then
    OriginalGoodPlaceCotangentNorms318.normalizer c (t u v) (hn c u v hf) w hw i
  else (OriginalConstructedExcludedGenerators318.generators c u v hf i).generator ⟨w,hw⟩
lemma normalizer_ne : normalizer c u v hf i w≠0 := by
  unfold normalizer
  split_ifs with hw
  · exact OriginalGoodPlaceCotangentNorms318.normalizer_ne c (t u v) (hn c u v hf) w hw i
  · exact (OriginalConstructedExcludedGenerators318.generators c u v hf i).nonzero ⟨w,hw⟩

/-- An actual valuation-ring SUBMODULE of the genuine number-field
cotangent-square fiber, not only a scalar-valued norm function. -/
@[expose] def lattice : Submodule R E :=
  (FinitePlacePrincipalLattice318.lattice w (normalizer c u v hf i w)).comap
    ((frame c (t u v) (hn c u v hf) i).restrictScalars R).toLinearMap

lemma mem_iff (x : E) : x∈lattice c u v hf i w ↔
    w (frame c (t u v) (hn c u v hf) i x)*(w (normalizer c u v hf i w))⁻¹≤1 :=
  FinitePlacePrincipalLattice318.mem_iff_norm w _ (normalizer_ne c u v hf i w) _

/-- Restriction of the actual generic fiber frame to its embedded
integral lattice. Both directions preserve the SAME valuation-ring action. -/
@[expose] def latticeMap : lattice c u v hf i w →ₗ[R]
    FinitePlacePrincipalLattice318.lattice w (normalizer c u v hf i w) :=
  (((frame c (t u v) (hn c u v hf) i).restrictScalars R).toLinearMap.comp
    (lattice c u v hf i w).subtype).codRestrict _ (fun x => x.property)
lemma latticeMap_bijective : Function.Bijective (latticeMap c u v hf i w) := by
  constructor
  · intro x y h
    apply Subtype.ext
    exact (frame c (t u v) (hn c u v hf) i).injective (congrArg Subtype.val h)
  · intro y
    refine ⟨⟨(frame c (t u v) (hn c u v hf) i).symm y.val,?_⟩,?_⟩
    · change frame c (t u v) (hn c u v hf) i
        ((frame c (t u v) (hn c u v hf) i).symm y.val)∈_
      simpa only [LinearEquiv.apply_symm_apply] using y.property
    · apply Subtype.ext
      exact (frame c (t u v) (hn c u v hf) i).apply_symm_apply y.val

/-- Produced free rank-one integral frame of the ACTUAL fiber lattice. -/
@[expose] def basis : R ≃ₗ[R] lattice c u v hf i w :=
  (FinitePlacePrincipalLattice318.basis w _ (normalizer_ne c u v hf i w)).trans
    (LinearEquiv.ofBijective (latticeMap c u v hf i w)
      (latticeMap_bijective c u v hf i w)).symm

lemma assembled_norm : OriginalFiniteNormAssembly318.finiteNorm c (t u v) (hn c u v hf) i
    (OriginalConstructedExcludedGenerators318.generators c u v hf i) w=
      (w (normalizer c u v hf i w))⁻¹ := by
  unfold OriginalFiniteNormAssembly318.finiteNorm normalizer
  split_ifs with hw <;> rfl

variable (hλ : lambda=2401) (hμ : mu= -343/32)
lemma norm_normalizer : (norms hλ hμ c u v hf i).finiteNorm w=
    (w (normalizer c u v hf i w))⁻¹ := assembled_norm c u v hf i w

/-- Membership in this actual submodule is exactly the already produced
finite-place bound for the coefficient of ANY vector of the whole fiber. -/
lemma mem_iff_produced_bound (x : E) : x∈lattice c u v hf i w ↔
    w (frame c (t u v) (hn c u v hf) i x)*(norms hλ hμ c u v hf i).finiteNorm w≤1 := by
  rw [mem_iff,norm_normalizer c u v hf i w hλ hμ]

/-- Literal fiber elements of both genuine J-squared global sections
belong to the actual free rank-one integral lattice at EVERY place,
including all places above2,3,5,7. No global proper regular-model or
Hodge/KS identification is asserted for these local lattices. -/
theorem original_global_sections_mem (n : Fin 2) :
    globalFiber c (t u v) (hn c u v hf) i
      (![ContactScaledBicanonicalPoint318.scaledQ0 c,
        ContactScaledBicanonicalPoint318.scaledQ1 c] n)∈lattice c u v hf i w := by
  rw [mem_iff,frame_globalFiber,←assembled_norm c u v hf i w]
  have hb := OriginalFiniteNormAssembly318.original_bound c (t u v) (hn c u v hf) i
    (OriginalConstructedExcludedGenerators318.generators c u v hf i) w n
  fin_cases n <;> exact hb
end OriginalIntrinsicFiniteLattices318
