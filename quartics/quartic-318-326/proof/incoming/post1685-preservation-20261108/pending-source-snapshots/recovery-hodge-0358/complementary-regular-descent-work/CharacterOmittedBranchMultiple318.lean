module
public import BranchGlobalDifferentialRestriction318
public import CharacterBranchActualRestriction318
public import RegularUnitMultiple318
public section
noncomputable section
namespace CharacterOmittedBranchMultiple318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
open BranchGlobalDifferentialRestriction318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
lemma own_normalized (i:Fin 4):CharacterBranchLocalForm318.form i i=
    (CharacterBranchLocalForm318.unitCoefficient i i*ContactFrameNormalization318.sourceCoordinate units i) •
      KaehlerDifferential.D ℚ (B i) (ContactFrameNormalization318.sourceCoordinate units i):=by
  apply (ContactDifferentialFrames318.sourceLocalizationFrame units i).injective
  rw [CharacterBranchLocalForm318.omitted_frame_value,map_smul,
    ContactFrameNormalization318.source_coordinate_normalized,smul_eq_mul,mul_one]
/-- At the only vanishing branch, actual kernel invariance gives regular
coordinate divisibility before taking a ratio with the known local form. -/
theorem form_multiple (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s):
    ∃a:B i,form i s=a • CharacterBranchLocalForm318.form i i:=by
  obtain ⟨a,ha⟩:=invariant_factorization i s h
  exact RegularUnitMultiple318.of_factorizations (K:=B i) (V:=KaehlerDifferential ℚ (B i))
    (ContactFrameNormalization318.sourceCoordinate units i) a (CharacterBranchLocalForm318.unitCoefficient i i)
    (form i s) (CharacterBranchLocalForm318.form i i)
    (KaehlerDifferential.D ℚ (B i) (ContactFrameNormalization318.sourceCoordinate units i))
    (CharacterBranchLocalForm318.unitCoefficient_unit i i) ha (own_normalized i)
/-- Actual entire-chart section equality with its scalar in the original
regular-function ring, retaining the already checked local normalization. -/
theorem section_multiple (i:Fin 4) (s:Γ(M,⊤)) (h:CharacterDifferentialInvariants318.Fixed i s):
    ∃a:Γ(X,j i ''ᵁ ⊤),M.presheaf.map (homOfLE (show j i ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op s=
      a • M.presheaf.map (homOfLE (show j i ''ᵁ ⊤≤(⊤:X.Opens) from le_top)).op
        (ContactCharacterDifferentials318.differential i):=by
  obtain ⟨a,ha⟩:=form_multiple i s h
  refine ⟨ScaledGlobalSectionRestriction318.scalar (j i) a,?_⟩
  have hm:=congrArg (IntrinsicChartSections318.sectionMap (Y:=X) (R:=ℚ) (S:=B i)
    (j i) p (ContactIntrinsicFrames318.branch_structure units i)) ha
  have hs:=IntrinsicChartSections318.section_smul (Y:=X) (R:=ℚ) (S:=B i)
    (j i) p (ContactIntrinsicFrames318.branch_structure units i) a
    (CharacterBranchLocalForm318.form i i)
  exact (form_restrict i s).symm.trans (hm.trans (hs.trans
    (congrArg (fun t:Γ(M,j i ''ᵁ ⊤)=>ScaledGlobalSectionRestriction318.scalar (j i) a • t)
      (CharacterBranchActualRestriction318.restrict i i).symm)))
end CharacterOmittedBranchMultiple318
