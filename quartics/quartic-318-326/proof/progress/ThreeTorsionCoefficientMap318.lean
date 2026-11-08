module
public import ThreeTorsionFunctor318
public import CompletedKernelBaseChange318
public section
noncomputable section
namespace ThreeTorsionCoefficientMap318
open Polynomial ThreeTorsionAlgebra318 ThreeTorsionFunctor318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R S:Type} [CommRing R] [CommRing S] [Algebra R S]
variable [Invertible (3:R)] [Invertible (3:S)] (A B:R) (hD:IsUnit (-16*(4*A^3+27*B^2)))
local notation "a" => algebraMap R S

lemma inverse_three_map : a (⅟(3:R))=⅟(3:S) := by
  calc
    a (⅟(3:R))=(⅟(3:S)*3)*a (⅟(3:R)) := by rw [invOf_mul_self,one_mul]
    _=⅟(3:S)*a ((3:R)*⅟(3:R)) := by rw [map_mul,map_ofNat,mul_assoc]
    _=⅟(3:S) := by rw [mul_invOf_self,map_one,mul_one]
lemma polynomial_map : (ShortThreeTorsion318.polynomial A B).map a=
    ShortThreeTorsion318.polynomial (a A) (a B) := by
  simp only [ShortThreeTorsion318.polynomial,Polynomial.map_sub,Polynomial.map_add,
    Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C,
    map_mul,map_pow,map_ofNat,Polynomial.map_ofNat,inverse_three_map]

abbrev Changed := Ring (a A) (a B) (CompletedKernelBaseChange318.mappedDiscriminant A B hD)
@[expose] def coefficientMap : Ring A B hD →ₐ[R] Changed (S:=S) A B hD :=
  toHom A B hD ⟨(x _ _ _,y _ _ _),by
    constructor
    · change (ShortThreeTorsion318.polynomial A B).eval₂ (algebraMap R (Changed A B hD)) (x _ _ _)=0
      rw [IsScalarTower.algebraMap_eq R S (Changed A B hD),←Polynomial.eval₂_map,polynomial_map]
      exact x_relation (a A) (a B) (CompletedKernelBaseChange318.mappedDiscriminant A B hD)
    · rw [IsScalarTower.algebraMap_apply R S (Changed A B hD) A,
        IsScalarTower.algebraMap_apply R S (Changed A B hD) B]
      exact equation _ _ _⟩
@[simp] lemma coefficientMap_x : coefficientMap (S:=S) A B hD (x A B hD)=
    x (a A) (a B) (CompletedKernelBaseChange318.mappedDiscriminant A B hD) := toHom_x _ _ _ _
@[simp] lemma coefficientMap_y : coefficientMap (S:=S) A B hD (y A B hD)=
    y (a A) (a B) (CompletedKernelBaseChange318.mappedDiscriminant A B hD) := toHom_y _ _ _ _
end ThreeTorsionCoefficientMap318
