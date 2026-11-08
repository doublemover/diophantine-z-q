module
public import CharacterBranchLocalForm318
public import CharacterCanonicalCommonRestriction318
public import FifthCommonScalarInjection318
public section
noncomputable section
namespace CharacterCommonScalarInjection318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev X:=ContactGlobalSmooth318.Model units
abbrev O:=ContactKummerOrder318.OpenOrder units
abbrev j:Spec (CommRingCat.of O)⟶X:=ContactOverlapIntrinsic318.embedding units
abbrev M:X.Modules:=ContactIntrinsicDifferentials318.omega units
lemma root_unit (i:Fin 4):IsUnit (ContactRootReciprocals318.openRoot units i):=by
  let k:=FifthFormLocalCoefficients318.chosen i
  have h:IsUnit (CharacterBranchLocalForm318.root i k):=
    ContactRootReciprocals318.branch_root_unit units i k
      (Ne.symm (FifthFormLocalCoefficients318.chosen_ne i))
  have hh:=h.map (ContactOverlapAlgebraMaps318.branchMap units k).toRingHom
  change IsUnit (ContactOverlapAlgebraMaps318.branchMap units k (CharacterBranchLocalForm318.root i k)) at hh
  rw [CharacterBranchLocalForm318.common_root] at hh
  exact hh
lemma coefficient_unit (i:Fin 4):IsUnit (ContactUnbranchedDifferentialFrame318.frame units
    (FifthFormCommonOpen318.form i)):=by
  rw [CharacterFifthCommonMultiple318.form_eq,map_smul,smul_eq_mul]
  exact (((CharacterFifthCommonMultiple318.factor_unit i).map (algebraMap ℚ O)).mul
    (root_unit i)).mul FifthCommonScalarInjection318.coefficient_unit
/-- Multiplication by each actual complementary pullback detects equality
of scalar sections on the entire genuine unbranched common chart. -/
theorem injective (i:Fin 4):Function.Injective (fun a:Γ(X,j ''ᵁ ⊤)=>a •
    M.presheaf.map (homOfLE (show j ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op
      (ContactCharacterDifferentials318.differential i)):=by
  rw [←CharacterCanonicalCommonRestriction318.restrict]
  exact IntrinsicChartScalarInjection318.injective (X:=X) (R:=ℚ) (S:=O) j
    (ContactIntrinsicDifferentials318.structureMap units) (ContactOverlapIntrinsic318.over_Q units)
    (ContactUnbranchedDifferentialFrame318.frame units) (FifthFormCommonOpen318.form i)
    (coefficient_unit i)
end CharacterCommonScalarInjection318
