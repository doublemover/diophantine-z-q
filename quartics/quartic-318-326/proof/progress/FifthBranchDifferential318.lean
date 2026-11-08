module
public import FifthBranchUnitCoefficient318
public section
noncomputable section
namespace FifthBranchDifferential318
open SourceTwistArithmetic318 FifthBranchUnitCoefficient318
set_option maxHeartbeats 550000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
local instance originalField:Field L:=(KummerTensorField318.source_raw_field units).toField
local instance rawCharZero:CharZero L:=Algebra.charZero_of_charZero (RatFunc ℚ) L
@[expose] def form (j:Fin 4):KaehlerDifferential ℚ (B j):=
  coefficient j • KaehlerDifferential.D ℚ (B j) (ContactFrameNormalization318.sourceCoordinate units j)
@[expose] def rootDerivative (j:Fin 4):O:=ContactUnbranchedDifferentialFrame318.frame units
  (AlgHomDifferential318.map (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing units j) (T:=ContactKummerOrder318.OpenOrder units) (ContactOverlapAlgebraMaps318.branchMap units j)
    (KaehlerDifferential.D ℚ (B j) (ContactFrameNormalization318.sourceCoordinate units j)))
lemma derivative_equation (j:Fin 4):
    (2*algebraMap ℚ O (↑((units j)⁻¹):ℚ)*
      ContactOverlapAlgebraMaps318.branchMap units j (ContactFrameNormalization318.sourceCoordinate units j))*
      rootDerivative j=1:=by
  have h:=congrArg (AlgHomDifferential318.map (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing units j) (T:=ContactKummerOrder318.OpenOrder units) (ContactOverlapAlgebraMaps318.branchMap units j))
    (ContactBranchDifferential318.D_branchT units j)
  simp only [AlgHomDifferential318.map_smul,AlgHomDifferential318.map_D,map_mul,map_ofNat,AlgHom.commutes] at h
  have hh:=congrArg (ContactUnbranchedDifferentialFrame318.frame units) h
  rw [ContactOverlapAlgebraMaps318.branchMap_coordinate] at hh
  have ht : ContactUnbranchedDifferentialFrame318.frame units
      (KaehlerDifferential.D ℚ O (SourceInfinityOverlap318.t units)) = 1 :=
    ContactUnbranchedDifferentialFrame318.frame_D units
  rw [ht] at hh
  simpa only [map_smul,smul_eq_mul,rootDerivative,AlgHomDifferential318.map_D] using hh.symm
lemma raw_derivative_equation (j:Fin 4):
    (algebraMap ℚ L (2*(↑((units j)⁻¹):ℚ))*InfinityFieldCoordinates318.root units j)*
      SourceOpenFractionField318.openEmbedding units (rootDerivative j)=1:=by
  have h:=congrArg (SourceOpenFractionField318.openEmbedding units) (derivative_equation j)
  simp only [map_mul,map_ofNat,map_one,RingHom.map_rat_algebraMap] at h
  have hr:=raw_coordinate j
  change SourceOpenFractionField318.openEmbedding units
    (ContactOverlapAlgebraMaps318.branchMap units j (ContactFrameNormalization318.sourceCoordinate units j))=_ at hr
  rw [hr] at h
  simpa only [map_mul,map_ofNat] using h
/-- The actual algebraic branch form restricts to the exact fifth quotient
pullback on the entire common open, with the full original-root normalization. -/
theorem common_eq (j:Fin 4):
    AlgHomDifferential318.map (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing units j) (T:=ContactKummerOrder318.OpenOrder units) (ContactOverlapAlgebraMaps318.branchMap units j) (form j)=
      FifthOverlapDifferentialEquation318.pulled:=by
  apply (ContactUnbranchedDifferentialFrame318.frame units).injective
  apply SourceOpenFractionField318.openEmbedding_injective units
  change SourceOpenFractionField318.openEmbedding units
    (ContactUnbranchedDifferentialFrame318.frame units
      (AlgHomDifferential318.map (R:=ℚ) (S:=ContactIntrinsicFrames318.BranchRing units j) (T:=ContactKummerOrder318.OpenOrder units) (ContactOverlapAlgebraMaps318.branchMap units j) (coefficient j • _)))=_
  rw [AlgHomDifferential318.map_smul,map_smul,smul_eq_mul,map_mul]
  change raw j (coefficient j)*SourceOpenFractionField318.openEmbedding units (rootDerivative j)=
    SourceOpenFractionField318.openEmbedding units FifthOverlapDifferentialEquation318.coefficient
  rw [raw_coefficient,FifthInvariantScalar318.raw_formula,scale_identity,map_mul]
  have h:=raw_derivative_equation j
  have hr:InfinityFieldCoordinates318.root units j≠0:=InfinityFieldCoordinates318.root_ne_zero units j
  have hc:ComplementCharacterIndependence318.root units j≠0:=CharacterRoot318.root_ne_zero _ _
  have hp:=FifthFormLocalCoefficients318.root_times_complement j
  rw [←hp]
  apply mul_right_cancel₀ (mul_ne_zero hr hc)
  simp only [mul_inv_rev]
  field_simp [hr,hc]
  linear_combination algebraMap ℚ L FifthInvariantScalar318.scale*h
/-- The actual branch frame coefficient is exactly the specified unit. -/
theorem frame_value (j:Fin 4):ContactDifferentialFrames318.sourceLocalizationFrame units j (form j)=coefficient j:=by
  rw [form,map_smul,smul_eq_mul,ContactFrameNormalization318.source_coordinate_normalized,mul_one]
end FifthBranchDifferential318
