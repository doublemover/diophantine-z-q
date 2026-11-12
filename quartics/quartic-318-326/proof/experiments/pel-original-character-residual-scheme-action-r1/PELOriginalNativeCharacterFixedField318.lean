module
public import PELOriginalCharacterNativeRank318
public import PELOriginalWholeCharacterDeck318
public section
noncomputable section
namespace PELOriginalNativeCharacterFixedField318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalCharacterPullback318
open PELOriginalCharacterQuotient318 PELOriginalMaximalQuotient318 OriginalContactInertiaBasis318
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩
local instance modelIntegral:IsIntegral Model:=FourRootWholeSchemeGeometry318.integral branches branches_injective
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2
local instance sourceOrderAlgebra:Algebra Source Model.functionField:=
  PELOriginalCharacterPullback318.sourceOrderAlgebra
local instance sourceRawAlgebra:Algebra Source Raw:=(FourRootActualGenericField318.affineEmbedding branches).toAlgebra
local instance targetOrderAlgebra (i:Fin 4):Algebra (PELOriginalCharacterFunctionField318.Order i)
    (Curve i).functionField:=PELOriginalCharacterFunctionField318.orderAlgebra i
local instance characterOrderAlgebra (i:Fin 4):Algebra (PELOriginalCharacterFunctionField318.Order i)
    (PELOriginalCharacterFunctionField318.Character i):=
  (PELOriginalOrderedCharacterFraction318.embedding i).toAlgebra

/-- The image of the actual native pullback, transported by the exact
source generic-stalk equivalence, is precisely the specified old character
subfield, not merely an isomorphic degree-two subextension. -/
theorem native_image_iff (i:Fin 4) (x:Raw):
    x∈Set.range (sourceEquiv.toRingHom.comp (pullback i).hom) ↔
      x∈PELOriginalActualCharacterFields318.field i:=by
  rw [actual_field_square]
  constructor
  · rintro ⟨y,rfl⟩
    exact (PELOriginalCharacterFunctionField318.characterEquiv i y).property
  · intro hx
    obtain ⟨y,hy⟩:=(PELOriginalCharacterFunctionField318.characterEquiv i).surjective ⟨x,hx⟩
    exact ⟨y,congrArg (fun z:PELOriginalCharacterFunctionField318.Character i=>(z:Raw)) hy⟩

/-- Function-field quotient identification for the original whole map.
This does not assert a categorical quotient property for arbitrary scheme
valued maps; it identifies the exact native image with the fixed field. -/
theorem native_image_fixed_field (i:Fin 4):
    Set.range (sourceEquiv.toRingHom.comp (pullback i).hom)=
      (IntermediateField.fixedField
        (PELOriginalActualCharacterFields318.field i).fixingSubgroup:Set Raw):=by
  rw [PELOriginalActualCharacterFields318.actual_fixed_field]
  ext x
  exact native_image_iff i x

/-- The field subgroup and whole-morphism stabilizer are BOTH the same
original analytic label kernel. The basis map is the old original one. -/
theorem original_kernel_identification (i:Fin 4) (g:Labels):
    (FourRootActualGenericSigns318.genericAutomorphism branches (basis g)∈
      (PELOriginalActualCharacterFields318.field i).fixingSubgroup ↔ g∈(character i).ker) ∧
    (FourRootSchemeSignAction318.action branches (basis g)≫morphism i=morphism i ↔
      g∈(character i).ker):=
  ⟨PELOriginalActualCharacterFields318.original_kernel i g,
    PELOriginalWholeCharacterDeck318.whole_deck_iff i g⟩
end PELOriginalNativeCharacterFixedField318
