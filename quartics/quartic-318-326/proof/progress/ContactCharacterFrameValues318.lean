module
public import ContactCharacterDifferentialNonzero318
public import ComplementCharacterIndependence318
public section
noncomputable section
namespace ContactCharacterFrameValues318
open Polynomial KaehlerDifferential SourceTwistArithmetic318 ContactKummerOrder318
open CharacterCoordinateDifferentials318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev O:=OpenOrder units
abbrev L:=ComplementCharacterIndependence318.L units
local instance field : Field L:=(KummerTensorField318.source_raw_field units).toField
local instance charZero : CharZero L:=Algebra.charZero_of_charZero (RatFunc ℚ) L

/-- Evaluate an actual affine differential in the whole unbranched dt frame. -/
@[expose] def openValue (ω:KaehlerDifferential ℚ S):O:=
  ContactUnbranchedDifferentialFrame318.frame units
    (AlgHomDifferential318.map (ContactUnbranchedDifferentialFrame318.toOpen units) ω)

/-- Retain the original contact-field embedding, not a newly selected field iso. -/
@[expose] def rawValue (ω:KaehlerDifferential ℚ S):L:=
  SourceOpenFractionField318.openEmbedding units (openValue ω)

theorem openValue_smul (s:S) (ω:KaehlerDifferential ℚ S):
    openValue (s • ω)=ContactUnbranchedDifferentialFrame318.toOpen units s*openValue ω:=by
  simp only [openValue,AlgHomDifferential318.map_smul,map_smul,smul_eq_mul]

theorem openValue_D_t : openValue (D ℚ S t)=1:=by
  unfold openValue
  rw [AlgHomDifferential318.map_D]
  change ContactUnbranchedDifferentialFrame318.frame units
    (D ℚ O (ContactUnbranchedDifferentialFrame318.toOpen units
      (algebraMap ℚ[X] S Polynomial.X)))=1
  rw [ContactUnbranchedDifferentialFrame318.toOpen_coordinate]
  exact ContactUnbranchedDifferentialFrame318.frame_D units

theorem embedding_z (i:Fin 4):
    SourceOpenFractionField318.openEmbedding units
      (ContactUnbranchedDifferentialFrame318.toOpen units (z i))=
        ComplementCharacterIndependence318.root units i:=by
  rw [show ContactUnbranchedDifferentialFrame318.toOpen units (z i)=
    SourceOpenFractionField318.orderToOpen units (z i) from rfl,
    SourceOpenFractionField318.openEmbedding_on_order]
  unfold z
  rw [SourceCharacterAlgebra318.toSource_embedding]
  exact CubicCharacterFraction318.embedding_root i

theorem raw_equation (i:Fin 4):
    (2*ComplementCharacterIndependence318.root units i)*
      rawValue (ContactCharacterAffinePullback318.finiteForm i)=
        algebraMap ℚ L (CharacterPublishedModels318.scaleUnit i:ℚ):=by
  have h:=congrArg openValue (CharacterPullbackNormalization318.finite_equation i)
  rw [openValue_smul,openValue_smul,openValue_D_t,mul_one,AlgHom.commutes] at h
  have he:=congrArg (SourceOpenFractionField318.openEmbedding units) h
  simp only [map_mul,map_ofNat] at he
  rw [embedding_z,RingHom.map_rat_algebraMap] at he
  exact he

/-- The coefficient of the actual pulled invariant form in dt, in the
original field, with its exact nonzero published coordinate scale. -/
theorem raw_formula (i:Fin 4):
    rawValue (ContactCharacterAffinePullback318.finiteForm i)=
      algebraMap ℚ L ((CharacterPublishedModels318.scaleUnit i:ℚ)/2)*
        (ComplementCharacterIndependence318.root units i)⁻¹:=by
  have hr:ComplementCharacterIndependence318.root units i≠0:=
    CharacterRoot318.root_ne_zero _ _
  apply mul_left_cancel₀ (mul_ne_zero (by norm_num : (2:L)≠0) hr)
  rw [raw_equation,map_div₀,map_ofNat]
  field_simp
end ContactCharacterFrameValues318
