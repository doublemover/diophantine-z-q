module
public import FifthOverlapDifferentialEquation318
public section
noncomputable section
namespace FifthInvariantScalar318
open SourceTwistArithmetic318 FifthCharacterShortPolynomial318 FifthOverlapCoordinates318
open FifthOverlapDifferentialEquation318
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
abbrev L:=FifthCharacterField318.L
local instance rawField:Field L:=(KummerTensorField318.source_raw_field units).toField
local instance rawCharZero:CharZero L:=Algebra.charZero_of_charZero (RatFunc ℚ) L
@[expose] def scale:ℚ:= -41160
lemma scale_identity: -(xScale:ℚ)/(2*(yScale:ℚ))=scale:=by
  norm_num [xScale,yScale,scale]
lemma solve {F:Type*} [Field F] (m n w r:F) (hn:2*n≠0) (hw:w≠0)
    (h:(2*n*w)*r= -m):r=(-m/(2*n))*w⁻¹:=by
  apply mul_right_cancel₀ (mul_ne_zero hn hw)
  calc
    r*(2*n*w)= -m:=by simpa only [mul_comm] using h
    _=((-m/(2*n))*w⁻¹)*(2*n*w):=by
      field_simp [hn,hw]
      rw [mul_assoc,mul_div_cancel_right₀ m hn]

/-- The exact pulled invariant coefficient in the original field. The
negative sign is forced by X=m/t+k, not chosen by a root convention. -/
theorem raw_formula:SourceOpenFractionField318.openEmbedding units coefficient=
    algebraMap ℚ L scale*FifthCharacterField318.root⁻¹:=by
  have h:=congrArg (SourceOpenFractionField318.openEmbedding units) normalized_equation
  simp only [map_mul,map_ofNat,map_neg,RingHom.map_rat_algebraMap,w_raw] at h
  have hn:(2:L)*algebraMap ℚ L (yScale:ℚ)≠0:=
    mul_ne_zero (by norm_num) (((Units.isUnit yScale).map (algebraMap ℚ L)).ne_zero)
  have hh:=solve (algebraMap ℚ L (xScale:ℚ)) (algebraMap ℚ L (yScale:ℚ))
    FifthCharacterField318.root (SourceOpenFractionField318.openEmbedding units coefficient)
    hn (CharacterRoot318.root_ne_zero _ _) h
  have hs: -(algebraMap ℚ L (xScale:ℚ))/(2*algebraMap ℚ L (yScale:ℚ))=
      algebraMap ℚ L scale:=by
    rw [←map_ofNat (algebraMap ℚ L) 2,←map_mul,←map_neg,←map_div₀,scale_identity]
  exact hh.trans (congrArg (fun a:L=>a*FifthCharacterField318.root⁻¹) hs)

/-- Equality in actual Kaehler differentials of the whole original open,
not merely proportionality of rational differential symbols. -/
theorem form_eq:pulled=algebraMap ℚ O scale • FifthGlobalIndependence318.form:=by
  apply (ContactUnbranchedDifferentialFrame318.frame units).injective
  apply SourceOpenFractionField318.openEmbedding_injective units
  rw [map_smul,smul_eq_mul,map_mul,RingHom.map_rat_algebraMap,FifthGlobalIndependence318.raw_formula]
  exact raw_formula
end FifthInvariantScalar318
