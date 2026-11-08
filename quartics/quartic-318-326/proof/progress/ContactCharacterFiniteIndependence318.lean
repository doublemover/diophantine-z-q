module
public import ContactCharacterFrameValues318
public section
noncomputable section
namespace ContactCharacterFiniteIndependence318
open scoped BigOperators
open SourceTwistArithmetic318 CharacterCoordinateDifferentials318
open ContactCharacterFrameValues318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
attribute [-instance] DivisionRing.toRatAlgebra
local instance field : Field L:=(KummerTensorField318.source_raw_field units).toField
local instance charZero : CharZero L:=Algebra.charZero_of_charZero (RatFunc ℚ) L

/-- The same original-field sign automorphism, with its forced Q-linearity. -/
@[expose] def sign (i:Fin 4):L≃ₐ[ℚ]L:=
  { (ComplementCharacterIndependence318.flip units i).toRingEquiv with
    commutes' := fun a=>RingHom.map_rat_algebraMap _ a }

theorem inverse_roots_independent (a:Fin 4→ℚ)
    (h:∑i,algebraMap ℚ L (a i)*(ComplementCharacterIndependence318.root units i)⁻¹=0):
    ∀i,a i=0:=by
  apply ComplementCharacterIndependence318.coefficients_zero
    (fun i=>(ComplementCharacterIndependence318.root units i)⁻¹)
    (fun i=>inv_ne_zero (CharacterRoot318.root_ne_zero _ _)) sign
    (fun i=>by
      change ComplementCharacterIndependence318.flip units i
        ((ComplementCharacterIndependence318.root units i)⁻¹)=_
      rw [map_inv₀,ComplementCharacterIndependence318.flip_self])
    (fun i j hij=>by
      change ComplementCharacterIndependence318.flip units i
        ((ComplementCharacterIndependence318.root units j)⁻¹)=_
      rw [map_inv₀]
      change (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units)
        (SourceCharacterFields318.flip i)
          (CharacterRoot318.root (SourceKummerField318.parameter units)
            (SourceCharacterFields318.complement j)))⁻¹=_
      rw [SourceCharacterFields318.other_flip_negates units j i hij,inv_neg]
      rfl) a h

/-- Rational independence of the actual four affine pulled forms, with
coefficients transported through the whole unbranched order and original field. -/
theorem finite_linear_independent (a:Fin 4→ℚ)
    (h:∑i,algebraMap ℚ S (a i) • ContactCharacterAffinePullback318.finiteForm i=0):
    ∀i,a i=0:=by
  have he:=congrArg rawValue h
  simp only [rawValue,openValue,map_sum,AlgHomDifferential318.map_smul,
    map_smul,smul_eq_mul,map_zero,AlgHom.commutes,map_mul,
    RingHom.map_rat_algebraMap] at he
  change ∑i,algebraMap ℚ L (a i)*rawValue
    (ContactCharacterAffinePullback318.finiteForm i)=0 at he
  simp only [raw_formula,←mul_assoc,←map_mul] at he
  have hz:=inverse_roots_independent
    (fun i=>a i*((CharacterPublishedModels318.scaleUnit i:ℚ)/2)) he
  intro i
  exact (mul_eq_zero.mp (hz i)).resolve_right
    (div_ne_zero (Units.ne_zero _) (by norm_num))
end ContactCharacterFiniteIndependence318
