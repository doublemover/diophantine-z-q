module
public import PELOriginalCharacterSectionInvariants318
public import InjectiveRingHomDescent318
public section
noncomputable section
namespace PELOriginalCharacterOpenDescent318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
open PELOriginalCharacterPullback318 PELOriginalGenericLabelsExhaustive318
open PELOriginalCharacterSectionInvariants318 PELOriginalCharacterNormalOpens318
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩
local instance sourceIntegral:IsIntegral Model:=FourRootWholeSchemeGeometry318.integral branches branches_injective
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2
local instance mapFinite (i:Fin 4):IsFinite (morphism i):=PELOriginalWholeCharacterFinite318.finite i
local instance mapDominant (i:Fin 4):IsDominant (morphism i):=PELOriginalWholeCharacterProper318.dominant i
variable {T:Type*} [CommRing T]

/-- Exact regular-section descent on the full inverse image of ANY
normal affine target open. Kernel invariance is tested in the original
field via actual native germs; it is not an extra generic-field model. -/
theorem existsUnique_factor (i:Fin 4) (U:(Curve i).Opens) [Nonempty U]
    [Nonempty (morphism i⁻¹ᵁU)] (hU:IsAffineOpen U) [IsIntegrallyClosed Γ(Curve i,U)]
    (f:T→+*Γ(Model,morphism i⁻¹ᵁU))
    (hf:∀x:T,∀g:Labels,g∈(character i).ker →
      originalAutomorphism g (originalGerm i U (f x))=originalGerm i U (f x)):
    ∃!k:T→+*Γ(Curve i,U),((morphism i).app U).hom.comp k=f:=by
  apply InjectiveRingHomDescent318.existsUnique_factor
    ((morphism i).app U).hom (FiniteNormalOpenImage318.app_injective (morphism i) U) f
  intro x
  exact (range_iff_original_kernel i U hU (f x)).mpr (hf x)

/-- This inverse image includes EVERY source point mapping to the target
infinity chart, not only the earlier explicitly localized neighborhood. -/
theorem infinity_image_iff (i:Fin 4)
    (x:Γ(Model,morphism i⁻¹ᵁinfinityOpen i)):
    letI:=infinity_nonempty i
    letI:=DominantFunctionField318.preimage_nonempty (morphism i) (infinityOpen i)
    x∈Set.range ((morphism i).app (infinityOpen i)).hom ↔
      ∀g:Labels,g∈(character i).ker →
        originalAutomorphism g (originalGerm i (infinityOpen i) x)=
          originalGerm i (infinityOpen i) x:=by
  letI:=infinity_nonempty i
  letI:=DominantFunctionField318.preimage_nonempty (morphism i) (infinityOpen i)
  letI:=infinity_normal i
  exact range_iff_original_kernel i (infinityOpen i) (infinity_affine i) x

/-- Both target charts satisfy the same exact regular-section image
criterion. The target cover, including infinity, is the original one. -/
theorem finite_image_iff (i:Fin 4)
    (x:Γ(Model,morphism i⁻¹ᵁfiniteOpen i)):
    letI:=finite_nonempty i
    letI:=DominantFunctionField318.preimage_nonempty (morphism i) (finiteOpen i)
    x∈Set.range ((morphism i).app (finiteOpen i)).hom ↔
      ∀g:Labels,g∈(character i).ker →
        originalAutomorphism g (originalGerm i (finiteOpen i) x)=
          originalGerm i (finiteOpen i) x:=by
  letI:=finite_nonempty i
  letI:=DominantFunctionField318.preimage_nonempty (morphism i) (finiteOpen i)
  letI:=finite_normal i
  exact range_iff_original_kernel i (finiteOpen i) (finite_affine i) x
attribute [local instance] infinity_nonempty infinity_normal
local instance infinityPreimageNonempty (i:Fin 4):
    Nonempty (morphism i⁻¹ᵁinfinityOpen i):=
  DominantFunctionField318.preimage_nonempty (morphism i) (infinityOpen i)

/-- The arbitrary-test-ring universal property holds on the FULL actual
infinity inverse image, not just on the earlier smaller neighborhood. -/
theorem infinity_existsUnique_factor (i:Fin 4)
    (f:T→+*Γ(Model,morphism i⁻¹ᵁinfinityOpen i))
    (hf:∀x:T,∀g:Labels,g∈(character i).ker →
      originalAutomorphism g (originalGerm i (infinityOpen i) (f x))=
        originalGerm i (infinityOpen i) (f x)):
    ∃!k:T→+*Γ(Curve i,infinityOpen i),
      ((morphism i).app (infinityOpen i)).hom.comp k=f:=
  existsUnique_factor i (infinityOpen i) (infinity_affine i) f hf
end PELOriginalCharacterOpenDescent318
