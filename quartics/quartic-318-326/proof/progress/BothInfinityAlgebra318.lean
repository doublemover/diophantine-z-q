module
public import InfinityVietaAlgebra318
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public section
noncomputable section
namespace BothInfinityAlgebra318
open scoped TensorProduct
open InfinityVietaAlgebra318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type u} [CommRing R]

abbrev PairRing (A B:R) := InfinityChart318.Ring A B ⊗[R] InfinityChart318.Ring A B
@[expose] def leftPair (A B:R) : InfinityChart318.Ring A B →ₐ[R] PairRing A B := Algebra.TensorProduct.includeLeft
@[expose] def rightPair (A B:R) : InfinityChart318.Ring A B →ₐ[R] PairRing A B := Algebra.TensorProduct.includeRight
@[expose] def coeff (A B:R) : R →ₐ[R] PairRing A B := Algebra.ofId R _
@[expose] def U1 (A B:R) := leftPair A B (InfinityChart318.x A B)
@[expose] def V1 (A B:R) := leftPair A B (InfinityChart318.z A B)
@[expose] def U2 (A B:R) := rightPair A B (InfinityChart318.x A B)
@[expose] def V2 (A B:R) := rightPair A B (InfinityChart318.z A B)
@[expose] def Q (A B:R) := q (coeff A B A) (coeff A B B) (U2 A B) (V1 A B) (V2 A B)
@[expose] def S (A B:R) := s (coeff A B A) (U1 A B) (U2 A B) (V1 A B)
@[expose] def C (A B:R) := Q A B^3+coeff A B A*(S A B)^2*Q A B+coeff A B B*(S A B)^3
@[expose] def domainElement (A B:R) := Q A B*C A B
abbrev OutputRing (A B:R) := Localization.Away (domainElement A B)
@[expose] def pairMap (A B:R) : PairRing A B →ₐ[R] OutputRing A B := IsScalarTower.toAlgHom R (PairRing A B) (OutputRing A B)

lemma left_pow (A B:R) (a:InfinityChart318.Ring A B) (n:ℕ) : leftPair A B (a^n)=(leftPair A B a)^n :=
  (leftPair A B).toRingHom.map_pow a n
lemma right_pow (A B:R) (a:InfinityChart318.Ring A B) (n:ℕ) : rightPair A B (a^n)=(rightPair A B a)^n :=
  (rightPair A B).toRingHom.map_pow a n
lemma pair_pow (A B:R) (a:PairRing A B) (n:ℕ) : pairMap A B (a^n)=(pairMap A B a)^n :=
  (pairMap A B).toRingHom.map_pow a n
lemma pair_one (A B:R) : pairMap A B 1=1 := (pairMap A B).toRingHom.map_one

lemma raw_first (A B:R) : equation (coeff A B A) (coeff A B B) (U1 A B) (V1 A B)=0 := by
  have h := congrArg (leftPair A B) (InfinityChart318.relation A B)
  simpa only [map_sub,map_pow,left_pow,right_pow,pair_pow,pair_one,map_mul,map_zero,AlgHom.commutes,equation,U1,V1,coeff,Algebra.ofId_apply] using h
lemma raw_second (A B:R) : equation (coeff A B A) (coeff A B B) (U2 A B) (V2 A B)=0 := by
  have h := congrArg (rightPair A B) (InfinityChart318.relation A B)
  simpa only [map_sub,map_pow,left_pow,right_pow,pair_pow,pair_one,map_mul,map_zero,AlgHom.commutes,equation,U2,V2,coeff,Algebra.ofId_apply] using h

lemma two_units (A B:R) : IsUnit (pairMap A B (Q A B)) ∧ IsUnit (pairMap A B (C A B)) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S:=OutputRing A B) (domainElement A B)
  change IsUnit (pairMap A B (Q A B*C A B)) at h
  rw [map_mul] at h
  exact ⟨isUnit_of_mul_isUnit_left h,isUnit_of_mul_isUnit_right h⟩
@[expose] def qUnit (A B:R) : (OutputRing A B)ˣ := (two_units A B).1.unit
@[expose] def u1 (A B:R) := pairMap A B (U1 A B)
@[expose] def v1 (A B:R) := pairMap A B (V1 A B)
@[expose] def u2 (A B:R) := pairMap A B (U2 A B)
@[expose] def v2 (A B:R) := pairMap A B (V2 A B)
@[expose] def slope (A B:R) := pairMap A B (S A B)*↑(qUnit A B)⁻¹
@[expose] def intercept (A B:R) := v1 A B-slope A B*u1 A B

lemma slope_Q (A B:R) : slope A B*pairMap A B (Q A B)=pairMap A B (S A B) := by
  rw [slope,mul_assoc,←(two_units A B).1.unit_spec]
  change pairMap A B (S A B)*(↑(qUnit A B)⁻¹*↑(qUnit A B))=_
  rw [Units.inv_mul,mul_one]

lemma map_Q (A B:R) : pairMap A B (Q A B)=
    q (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (u2 A B) (v1 A B) (v2 A B) := by
  simp only [Q,q,u2,v1,v2,map_sub,map_one,map_mul,map_add,map_pow,left_pow,right_pow,pair_pow,pair_one,coeff,AlgHom.commutes,Algebra.ofId_apply]
lemma map_S (A B:R) : pairMap A B (S A B)=
    s (algebraMap R (OutputRing A B) A) (u1 A B) (u2 A B) (v1 A B) := by
  simp only [S,s,u1,u2,v1,map_add,map_mul,map_pow,left_pow,right_pow,pair_pow,pair_one,coeff,AlgHom.commutes,Algebra.ofId_apply]

lemma mapped_first (A B:R) : equation (algebraMap R (OutputRing A B) A)
    (algebraMap R (OutputRing A B) B) (u1 A B) (v1 A B)=0 := by
  have h := congrArg (pairMap A B) (raw_first A B)
  simpa only [equation,map_sub,map_pow,left_pow,right_pow,pair_pow,pair_one,map_mul,map_zero,coeff,AlgHom.commutes,Algebra.ofId_apply,u1,v1] using h
lemma mapped_second (A B:R) : equation (algebraMap R (OutputRing A B) A)
    (algebraMap R (OutputRing A B) B) (u2 A B) (v2 A B)=0 := by
  have h := congrArg (pairMap A B) (raw_second A B)
  simpa only [equation,map_sub,map_pow,left_pow,right_pow,pair_pow,pair_one,map_mul,map_zero,coeff,AlgHom.commutes,Algebra.ofId_apply,u2,v2] using h

lemma slope_relation (A B:R) : slope A B*q (algebraMap R (OutputRing A B) A)
    (algebraMap R (OutputRing A B) B) (u2 A B) (v1 A B) (v2 A B)=
    s (algebraMap R (OutputRing A B) A) (u1 A B) (u2 A B) (v1 A B) := by
  rw [←map_Q,←map_S,slope_Q]

lemma line_first (A B:R) : v1 A B=slope A B*u1 A B+intercept A B := by rw [intercept]; ring
lemma line_second (A B:R) : v2 A B=slope A B*u2 A B+intercept A B := by
  have hq : IsUnit (q (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B)
      (u2 A B) (v1 A B) (v2 A B)) := by rw [←map_Q]; exact (two_units A B).1
  have hh := line_relation _ _ _ _ _ _ _ (mapped_first A B) (mapped_second A B) hq (slope_relation A B)
  rw [intercept]
  linear_combination -hh

lemma cubic_coefficient_identity (A B:R) :
    c (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B)*
      (pairMap A B (Q A B))^3=pairMap A B (C A B) := by
  simp only [C,map_add,map_mul,map_pow,left_pow,right_pow,pair_pow,pair_one,coeff,AlgHom.commutes,Algebra.ofId_apply]
  rw [←slope_Q A B]
  simp only [c]
  ring
lemma cubic_coefficient_unit (A B:R) : IsUnit
    (c (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B)) := by
  apply isUnit_of_mul_isUnit_left (y:=(pairMap A B (Q A B))^3)
  rw [cubic_coefficient_identity]
  exact (two_units A B).2
@[expose] def cubicUnit (A B:R) : (OutputRing A B)ˣ := (cubic_coefficient_unit A B).unit
@[expose] def outU (A B:R) := u1 A B+u2 A B+
    d (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B) (intercept A B)*↑(cubicUnit A B)⁻¹
@[expose] def outV (A B:R) := slope A B*outU A B-intercept A B

lemma output_equation (A B:R) : equation (algebraMap R (OutputRing A B) A)
    (algebraMap R (OutputRing A B) B) (outU A B) (outV A B)=0 := by
  apply InfinityVietaAlgebra318.output_equation _ _ _ _ _ _ _ _ _ _ (mapped_first A B)
    (line_first A B) (line_second A B) (slope_relation A B)
  · rw [outU]
    have hu := Units.mul_inv (cubicUnit A B)
    have hval : (↑(cubicUnit A B) : OutputRing A B)=
      c (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B) (slope A B) :=
        (cubic_coefficient_unit A B).unit_spec
    rw [hval] at hu
    linear_combination d (algebraMap R (OutputRing A B) A) (algebraMap R (OutputRing A B) B)
      (slope A B) (intercept A B)*hu
  · rfl

/-- Actual coordinate-algebra map for the regular both-infinity addition chart. -/
@[expose] def outputMap (A B:R) : InfinityChart318.Ring A B →ₐ[R] OutputRing A B :=
  InfinityChart318.lift A B (outU A B) (outV A B) (output_equation A B)

end BothInfinityAlgebra318
