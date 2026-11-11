module
public import ThreeJComplexFibers318
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.LinearAlgebra.Dimension.Free
public section
noncomputable section
namespace ThreeJMonicAlgebra318
open Polynomial
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The coefficient variable is j; the outer polynomial variable is T. -/
abbrev Base := ℚ[X]
@[expose] def polynomial : Base[X] :=
  X^4+C (756-X)*X^3+C 196830*X^2+C 19131876*X+C 387420489
abbrev Model := AdjoinRoot polynomial
@[expose] def t : Model := AdjoinRoot.root polynomial
@[expose] def j : Model := algebraMap Base Model X

lemma monic : polynomial.Monic := by unfold polynomial; monicity!
lemma degree : polynomial.natDegree=4 := by unfold polynomial; compute_degree!
instance model_finite : Module.Finite Base Model := monic.finite_adjoinRoot
instance model_free : Module.Free Base Model := monic.free_adjoinRoot
lemma rank_four : Module.finrank Base Model=4 := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' monic).basis,Fintype.card_fin]
  exact degree

/-- The monic equation uses the exact original numerator, without changing
its scale or choosing a different base coordinate. -/
lemma relation : t^4+(756-j)*t^3+196830*t^2+19131876*t+387420489=0 := by
  have h := AdjoinRoot.eval₂_root polynomial
  change polynomial.eval₂ (algebraMap Base Model) t=0 at h
  simpa only [polynomial,eval₂_add,eval₂_sub,eval₂_mul,eval₂_pow,eval₂_X,eval₂_C,eval₂_ofNat,
    map_sub,map_ofNat,j] using h

lemma numerator_relation : (t+27)*(t+243)^3=j*t^3 := by
  linear_combination relation

@[expose] def inverseT : Model := algebraMap ℚ Model (-1/387420489) *
  (t^3+(756-j)*t^2+196830*t+19131876)

lemma t_inverseT : t*inverseT=1 := by
  have h : t*(t^3+(756-j)*t^2+196830*t+19131876)= -(387420489:Model) := by
    linear_combination relation
  have hc : algebraMap ℚ Model (-1/387420489)*(387420489:Model)= -1 := by
    calc
      _ = algebraMap ℚ Model ((-1/387420489)*(387420489:ℚ)) := by rw [map_mul,map_ofNat]
      _ = -1 := by norm_num
  calc
    t*inverseT=algebraMap ℚ Model (-1/387420489)*
      (t*(t^3+(756-j)*t^2+196830*t+19131876)) := by unfold inverseT; ring
    _ = algebraMap ℚ Model (-1/387420489)*(-(387420489:Model)) := by rw [h]
    _ = 1 := by rw [mul_neg,hc,neg_neg]

lemma t_unit : IsUnit t := IsUnit.of_mul_eq_one inverseT t_inverseT

/-- The original rational expression becomes the actual coefficient j in
this algebra, with the inverse of T constructed from the monic relation. -/
lemma j_expression : (t+27)*(t+243)^3*inverseT^3=j := by
  rw [numerator_relation]
  calc
    j*t^3*inverseT^3=j*(t*inverseT)^3 := by ring
    _ = j := by rw [t_inverseT,one_pow,mul_one]

end ThreeJMonicAlgebra318
