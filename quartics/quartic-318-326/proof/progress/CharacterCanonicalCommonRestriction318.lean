module
public import CharacterFifthCommonMultiple318
public section
noncomputable section
namespace CharacterCanonicalCommonRestriction318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev X:=ContactGlobalSmooth318.Model units
abbrev O:=ContactKummerOrder318.OpenOrder units
abbrev j:Spec (CommRingCat.of O)⟶X:=ContactOverlapIntrinsic318.embedding units
abbrev p:X⟶Spec (CommRingCat.of ℚ):=ContactIntrinsicDifferentials318.structureMap units
abbrev M:X.Modules:=ContactIntrinsicDifferentials318.omega units
/-- Canonical whole-common-open presentation of the four original actual
pullback sections, with no change of map or normalization. -/
theorem restrict (i:Fin 4):
    IntrinsicChartSections318.sectionMap (Y:=X) (R:=ℚ) (S:=O) j p
      (ContactOverlapIntrinsic318.over_Q units) (FifthFormCommonOpen318.form i)=
    M.presheaf.map (homOfLE (show (j ''ᵁ (⊤:(Spec (CommRingCat.of O)).Opens))≤(⊤:X.Opens)
      from le_top)).op (ContactCharacterDifferentials318.differential i):=
  (FifthFormCommonOpen318.global_restrict i).symm
end CharacterCanonicalCommonRestriction318
