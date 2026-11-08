module
public import FifthFormGlobalRestriction318
public import FifthInvariantScalar318
public section
noncomputable section
namespace CharacterFifthCommonMultiple318
open AlgebraicGeometry CategoryTheory Opposite SourceTwistArithmetic318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev O:=ContactKummerOrder318.OpenOrder units
abbrev L:=FifthCharacterField318.L
local instance rawField:Field L:=(KummerTensorField318.source_raw_field units).toField
local instance rawCharZero:CharZero L:=Algebra.charZero_of_charZero (RatFunc ℚ) L
/-- The literal normalization relating a complementary invariant to the
already specified fifth invariant. Its sign and denominator are retained. -/
@[expose] def factor (i:Fin 4):ℚ:=
  (CharacterPublishedModels318.scaleUnit i:ℚ)/(2*FifthInvariantScalar318.scale)
lemma factor_unit (i:Fin 4):IsUnit (factor i):=by
  apply isUnit_iff_ne_zero.mpr
  exact div_ne_zero (Units.ne_zero _) (mul_ne_zero (by norm_num) (by norm_num [FifthInvariantScalar318.scale]))
lemma raw_relation (i:Fin 4):
    ContactCharacterFrameValues318.rawValue (ContactCharacterAffinePullback318.finiteForm i)=
      algebraMap ℚ L (factor i)*InfinityFieldCoordinates318.root units i*
        SourceOpenFractionField318.openEmbedding units FifthOverlapDifferentialEquation318.coefficient:=by
  rw [ContactCharacterFrameValues318.raw_formula,FifthInvariantScalar318.raw_formula,
    ←FifthFormLocalCoefficients318.root_times_complement i]
  have hx:=InfinityFieldCoordinates318.root_ne_zero units i
  have hy:=CharacterRoot318.root_ne_zero (SourceKummerField318.parameter units) (Finset.univ.erase i)
  change _=algebraMap ℚ L (factor i)*InfinityFieldCoordinates318.root units i*
    (algebraMap ℚ L FifthInvariantScalar318.scale*
      (InfinityFieldCoordinates318.root units i*ComplementCharacterIndependence318.root units i)⁻¹)
  have hs:algebraMap ℚ L FifthInvariantScalar318.scale≠0:=by
    norm_num [FifthInvariantScalar318.scale]
  rw [factor,map_div₀,map_div₀,map_mul,map_ofNat]
  change algebraMap ℚ L (↑(CharacterPublishedModels318.scaleUnit i):ℚ)/2*
      (ComplementCharacterIndependence318.root units i)⁻¹=_
  have hy':ComplementCharacterIndependence318.root units i≠0:=hy
  field_simp [hx,hy',hs]
/-- Equality in actual universal differentials on the complete common open,
not merely proportionality after a newly chosen field identification. -/
theorem form_eq (i:Fin 4):FifthFormCommonOpen318.form i=
    (algebraMap ℚ O (factor i)*ContactRootReciprocals318.openRoot units i) •
      FifthOverlapDifferentialEquation318.pulled:=by
  apply (ContactUnbranchedDifferentialFrame318.frame units).injective
  apply SourceOpenFractionField318.openEmbedding_injective units
  rw [map_smul,smul_eq_mul,map_mul,map_mul,RingHom.map_rat_algebraMap,
    ContactRootReciprocals318.open_embedding_root]
  exact raw_relation i
end CharacterFifthCommonMultiple318
