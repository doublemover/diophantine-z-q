module
public import CharacterPullbackNormalization318
public import ContactUnbranchedDifferentialFrame318
public section
noncomputable section
namespace ContactCharacterDifferentialNonzero318
open AlgebraicGeometry CategoryTheory Opposite KaehlerDifferential SourceTwistArithmetic318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

theorem finite_ne_zero (i:Fin 4) : ContactCharacterAffinePullback318.finiteForm i≠0 := by
  intro hz
  have h:=CharacterPullbackNormalization318.finite_equation i
  rw [hz,smul_zero] at h
  have hu:=((CharacterPublishedModels318.scaleUnit i).isUnit.map
    (algebraMap ℚ CharacterCoordinateDifferentials318.S))
  have he : KaehlerDifferential.D ℚ CharacterCoordinateDifferentials318.S
      CharacterCoordinateDifferentials318.t=0 :=
    hu.smul_left_cancel.mp (h.symm.trans (smul_zero _).symm)
  exact ContactUnbranchedDifferentialFrame318.D_t_ne_zero units he

/-- Each of the four actual globally pulled elliptic invariant differentials
is nonzero on the complete contact source. -/
theorem global_ne_zero (i:Fin 4) : ContactCharacterDifferentials318.differential i≠0 := by
  intro hz
  have h:=ContactCharacterAffinePullback318.finite_restrict i
  rw [hz,map_zero] at h
  have he:= (IntrinsicAffineSectionEquiv318.sectionMap_bijective
    (SourceGlobalAffine318.chartEmbedding units) (ContactIntrinsicDifferentials318.structureMap units)
      (SourceGlobalAffine318.chartEmbedding_over_Q units)).1
      (h.trans (map_zero _).symm)
  exact finite_ne_zero i he
end ContactCharacterDifferentialNonzero318
