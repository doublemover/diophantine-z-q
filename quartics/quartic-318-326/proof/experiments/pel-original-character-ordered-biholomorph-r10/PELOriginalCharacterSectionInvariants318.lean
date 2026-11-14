module
public import FiniteNormalOpenImage318
public import PELOriginalCharacterNormalOpens318
public import PELOriginalCharacterRegularInvariants318
public section
noncomputable section
namespace PELOriginalCharacterSectionInvariants318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
open PELOriginalCharacterPullback318 PELOriginalActualCharacterFields318
open PELOriginalGenericLabelsExhaustive318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩
local instance sourceIntegral:IsIntegral Model:=FourRootWholeSchemeGeometry318.integral branches branches_injective
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2
local instance mapFinite (i:Fin 4):IsFinite (morphism i):=PELOriginalWholeCharacterFinite318.finite i
local instance mapDominant (i:Fin 4):IsDominant (morphism i):=PELOriginalWholeCharacterProper318.dominant i

variable (i:Fin 4) (U:(Curve i).Opens) [Nonempty U] [Nonempty (morphism i⁻¹ᵁU)]
/-- Every section on the FULL inverse-image open is embedded in the
same original full field by its actual germ and previous native equivalence. -/
@[expose] def originalGerm:Γ(Model,morphism i⁻¹ᵁU)→+*Raw:=
  sourceEquiv.toRingHom.comp (Model.germToFunctionField (morphism i⁻¹ᵁU)).hom
lemma originalGerm_injective:Function.Injective (originalGerm i U):=
  sourceEquiv.injective.comp (Model.germToFunctionField_injective _)

/-- Native finite-normal descent upgrades the old generic image theorem
to sections on ANY specified normal affine target open. -/
theorem range_iff (hU:IsAffineOpen U) [IsIntegrallyClosed Γ(Curve i,U)]
    (x:Γ(Model,morphism i⁻¹ᵁU)):
    x∈Set.range ((morphism i).app U).hom ↔ originalGerm i U x∈field i:=by
  rw [FiniteNormalOpenImage318.range_iff (morphism i) U hU]
  constructor
  · rintro ⟨z,hz⟩
    apply (PELOriginalNativeCharacterFixedField318.native_image_iff i _).mp
    exact ⟨z,congrArg sourceEquiv hz⟩
  · intro hx
    obtain ⟨z,hz⟩:=(PELOriginalNativeCharacterFixedField318.native_image_iff i _).mpr hx
    exact ⟨z,sourceEquiv.injective hz⟩

/-- The fixed-field test is equivalent to ALL original kernel labels,
not merely a selected set of generators or an abstract order8 subgroup. -/
lemma originalGerm_mem_iff (x:Γ(Model,morphism i⁻¹ᵁU)):
    originalGerm i U x∈field i ↔ ∀g:Labels,g∈(character i).ker →
      originalAutomorphism g (originalGerm i U x)=originalGerm i U x:=by
  rw [←PELOriginalActualCharacterFields318.actual_fixed_field i,
    IntermediateField.mem_fixedField_iff]
  constructor
  · intro h g hg
    exact h _ ((PELOriginalActualCharacterFields318.original_kernel i g).mpr hg)
  · intro h σ hσ
    obtain ⟨g,hg,he⟩:=fixing_surjective i ⟨σ,hσ⟩
    rw [←he]
    exact h g hg

theorem range_iff_original_kernel (hU:IsAffineOpen U) [IsIntegrallyClosed Γ(Curve i,U)]
    (x:Γ(Model,morphism i⁻¹ᵁU)):
    x∈Set.range ((morphism i).app U).hom ↔ ∀g:Labels,g∈(character i).ker →
      originalAutomorphism g (originalGerm i U x)=originalGerm i U x:=by
  rw [range_iff i U hU,originalGerm_mem_iff]
end PELOriginalCharacterSectionInvariants318
