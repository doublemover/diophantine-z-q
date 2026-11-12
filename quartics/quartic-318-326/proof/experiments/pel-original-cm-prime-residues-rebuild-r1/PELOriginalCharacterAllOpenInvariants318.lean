module
public import FiniteNormalAllOpenImage318
public import PELOriginalCharacterNormalBasis318
public import PELOriginalCharacterOpenDescent318
public section
noncomputable section
namespace PELOriginalCharacterAllOpenInvariants318
open AlgebraicGeometry CategoryTheory
open PELOriginalCommonContactBase318 PELOriginalWholeCharacterMorphisms318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
open PELOriginalCharacterPullback318 PELOriginalActualCharacterFields318
open PELOriginalGenericLabelsExhaustive318 PELOriginalCharacterSectionInvariants318
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩
local instance sourceIntegral:IsIntegral Model:=FourRootWholeSchemeGeometry318.integral branches branches_injective
local instance targetIntegral (i:Fin 4):IsIntegral (Curve i):=
  (PELOriginalWholeCharacterProper318.target_proper_integral i).2
local instance mapFinite (i:Fin 4):IsFinite (morphism i):=PELOriginalWholeCharacterFinite318.finite i
local instance mapDominant (i:Fin 4):IsDominant (morphism i):=PELOriginalWholeCharacterProper318.dominant i

/-- No affine hypothesis remains: the whole target normal basis and
actual sheaf gluing are consumed for each nonempty target open. -/
theorem range_iff_nonempty (i:Fin 4) (U:(Curve i).Opens) [Nonempty U]
    [Nonempty (morphism i⁻¹ᵁU)] (x:Γ(Model,morphism i⁻¹ᵁU)):
    x∈Set.range ((morphism i).app U).hom ↔ ∀g:Labels,g∈(character i).ker →
      originalAutomorphism g (originalGerm i U x)=originalGerm i U x:=by
  rw [←originalGerm_mem_iff]
  rw [FiniteNormalAllOpenImage318.range_iff (morphism i)
    (PELOriginalCharacterNormalBasis318.hasBasis i) U]
  constructor
  · rintro ⟨z,hz⟩
    apply (PELOriginalNativeCharacterFixedField318.native_image_iff i _).mp
    exact ⟨z,congrArg sourceEquiv hz⟩
  · intro hx
    obtain ⟨z,hz⟩:=(PELOriginalNativeCharacterFixedField318.native_image_iff i _).mpr hx
    exact ⟨z,sourceEquiv.injective hz⟩

/-- On an empty open the condition is vacuous and its section is unique;
no generic germ of an empty open is introduced. -/
def Invariant (i:Fin 4) (U:(Curve i).Opens) (x:Γ(Model,morphism i⁻¹ᵁU)):Prop:=
  ∀h:Nonempty U,
    letI:=h
    letI:=DominantFunctionField318.preimage_nonempty (morphism i) U
    ∀g:Labels,g∈(character i).ker →
      originalAutomorphism g (originalGerm i U x)=originalGerm i U x

theorem range_iff (i:Fin 4) (U:(Curve i).Opens) (x:Γ(Model,morphism i⁻¹ᵁU)):
    x∈Set.range ((morphism i).app U).hom ↔ Invariant i U x:=by
  classical
  by_cases h:Nonempty U
  · letI:=h
    letI:=DominantFunctionField318.preimage_nonempty (morphism i) U
    constructor
    · intro hx h'
      exact (range_iff_nonempty i U x).mp hx
    · intro hx
      exact (range_iff_nonempty i U x).mpr (hx h)
  · have hu:U=⊥:=by
      apply le_antisymm _ bot_le
      intro p hp
      exact (h ⟨⟨p,hp⟩⟩).elim
    haveI:Subsingleton Γ(Model,morphism i⁻¹ᵁU):=by
      rw [hu,Scheme.Hom.preimage_bot]
      infer_instance
    exact ⟨fun _ h'=>False.elim (h h'),fun _=>⟨0,Subsingleton.elim _ _⟩⟩

theorem app_injective (i:Fin 4) (U:(Curve i).Opens):
    Function.Injective ((morphism i).app U).hom:=by
  classical
  by_cases h:Nonempty U
  · letI:=h
    letI:=DominantFunctionField318.preimage_nonempty (morphism i) U
    exact FiniteNormalOpenImage318.app_injective (morphism i) U
  · have hu:U=⊥:=by
      apply le_antisymm _ bot_le
      intro p hp
      exact (h ⟨⟨p,hp⟩⟩).elim
    haveI:Subsingleton Γ(Curve i,U):=by rw [hu];infer_instance
    exact fun _ _ _=>Subsingleton.elim _ _

/-- Restriction preserves the literal original germ, so kernel
invariance is compatible with ALL restrictions, including empty opens. -/
theorem invariant_restrict (i:Fin 4) {U V:(Curve i).Opens} (j:U⟶V)
    (x:Γ(Model,morphism i⁻¹ᵁV)) (hx:Invariant i V x):
    Invariant i U (Model.presheaf.map (homOfLE ((morphism i).preimage_mono j.le)).op x):=by
  intro hU
  letI:=hU
  letI:Nonempty V:=by obtain ⟨p⟩:=hU;exact ⟨⟨p.val,j.le p.property⟩⟩
  letI:=DominantFunctionField318.preimage_nonempty (morphism i) U
  letI:=DominantFunctionField318.preimage_nonempty (morphism i) V
  intro g hg
  have he:originalGerm i U
      (Model.presheaf.map (homOfLE ((morphism i).preimage_mono j.le)).op x)=
      originalGerm i V x:=
    congrArg sourceEquiv (AffineDominantNormRestriction318.germ_restrict Model _ x)
  rw [he]
  exact hx inferInstance g hg
end PELOriginalCharacterAllOpenInvariants318
