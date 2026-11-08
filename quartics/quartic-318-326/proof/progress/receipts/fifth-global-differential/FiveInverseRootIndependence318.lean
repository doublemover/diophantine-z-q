module
public import FiveCharacterIndependence318
public section
noncomputable section
namespace FiveInverseRootIndependence318
open SourceTwistArithmetic318 ContactCharacterFrameValues318
open scoped BigOperators
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
attribute [-instance] DivisionRing.toRatAlgebra
local instance field : Field L:=(KummerTensorField318.source_raw_field units).toField
local instance charZero : CharZero L:=Algebra.charZero_of_charZero (RatFunc ℚ) L
lemma full_root_neg (i:Fin 4):ContactCharacterFiniteIndependence318.sign i
    FifthCharacterField318.root= -FifthCharacterField318.root:=by
  change FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units)
    (SourceCharacterFields318.flip i) (CharacterRoot318.root _ Finset.univ)=_
  rw [CharacterRoot318.sign_action]
  have hs:CharacterRoot318.sign (F:=RatFunc ℚ) Finset.univ (SourceCharacterFields318.flip i)= -1:=by
    fin_cases i <;> norm_num [CharacterRoot318.sign,SourceCharacterFields318.flip,Fin.prod_univ_succ]
  rw [hs,map_neg,map_one,neg_one_mul]
  rfl

theorem independent (a:Fin 4→ℚ) (b:ℚ)
    (h:(∑i,algebraMap ℚ L (a i)*(ComplementCharacterIndependence318.root units i)⁻¹)+
      algebraMap ℚ L b*FifthCharacterField318.root⁻¹=0):
    (∀i,a i=0) ∧ b=0:=by
  apply FiveCharacterIndependence318.coefficients_zero
    (fun i=>(ComplementCharacterIndependence318.root units i)⁻¹)
    (fun i=>inv_ne_zero (CharacterRoot318.root_ne_zero _ _))
    FifthCharacterField318.root⁻¹ (inv_ne_zero (CharacterRoot318.root_ne_zero _ _))
    ContactCharacterFiniteIndependence318.sign
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
      rfl)
    (fun i=>by rw [map_inv₀,full_root_neg,inv_neg]) a b h
end FiveInverseRootIndependence318
