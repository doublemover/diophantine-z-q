module
public import LinearContactSquareclass318
public import Mathlib.Tactic
public section
noncomputable section
namespace SourceTwistArithmetic318
set_option maxHeartbeats 800000
open Polynomial
@[expose] def constants : Fin 4→ℚ := ![-14,-6,42,-21]
theorem constants_ne_zero (i:Fin 4) : constants i≠0 := by fin_cases i <;> norm_num [constants]
@[expose] def units (i:Fin 4) : ℚˣ := Units.mk0 (constants i) (constants_ne_zero i)
@[simp] theorem units_val (i:Fin 4) : (units i:ℚ)=constants i := rfl
@[expose] def complement : Fin 4→Fin 3→Fin 4 :=
  ![![1,2,3],![0,2,3],![0,1,3],![0,1,2]]
@[expose] def twistProducts (i:Fin 4) : ℚ := ∏j:Fin 3,constants (complement i j)
@[expose] def cubic (i:Fin 4) : ℚ[X] :=
  ∏j:Fin 3,(X-C (LinearContactSquareclass318.contacts (complement i j)))
@[expose] def centroid (i:Fin 4) : ℚ :=
  (∑j:Fin 3,LinearContactSquareclass318.contacts (complement i j))/3
@[expose] def cubicA : Fin 4→ℚ :=
  ![-1975726875,-5929627249/3,-129649/3,-5900698624/3]
@[expose] def cubicB : Fin 4→ℚ :=
  ![-33798988093750,-913149747428114/27,90882286/27,-906535659044864/27]
/-- Independently published Table 3 short-Weierstrass coefficients, ordered
by omitted finite contact 0,32,76832,-343 (labels 105,70,42,30). -/
@[expose] def publishedA : Fin 4→ℚ :=
  ![-1053721/3,-50401/3,-129649/3,-5762401/3]
@[expose] def publishedB : Fin 4→ℚ :=
  ![-2163135238/27,-22628702/27,-90882286/27,-27665272798/27]
@[expose] def jacobianTwist : Fin 4→ℚ := ![1/75,1/343,-1,1/32]
@[expose] def coordinateScale : Fin 4→ℚ := ![630,2058,42,336]
@[expose] def twistClasses : Fin 4→ℚ := ![3,7,-1,2]
@[expose] def twistSquare : Fin 4→ℚ := ![1/15,1/49,1,1/8]

theorem cubic_depression (i:Fin 4) :
    (cubic i).comp (X+C (centroid i))=X^3+C (cubicA i)*X+C (cubicB i) := by
  apply Polynomial.funext
  intro x
  fin_cases i <;> norm_num [cubic,centroid,complement,LinearContactSquareclass318.contacts,
    cubicA,cubicB,Fin.prod_univ_succ,Fin.sum_univ_succ,Polynomial.eval_comp] <;> ring

theorem published_twist_exact (i:Fin 4) :
    publishedA i=jacobianTwist i^2*cubicA i ∧
    publishedB i=jacobianTwist i^3*cubicB i := by
  fin_cases i <;> norm_num [publishedA,publishedB,jacobianTwist,cubicA,cubicB]

theorem jacobian_twist_class (i:Fin 4) :
    jacobianTwist i=twistClasses i*twistSquare i^2 := by
  fin_cases i <;> norm_num [jacobianTwist,twistClasses,twistSquare]

theorem complementary_twist_class (i:Fin 4) :
    twistProducts i=twistClasses i*42^2 := by
  fin_cases i <;> norm_num [twistProducts,constants,complement,twistClasses,Fin.prod_univ_succ]

theorem complementary_twist_exact (i:Fin 4) :
    twistProducts i=jacobianTwist i*coordinateScale i^2 := by
  fin_cases i <;> norm_num [twistProducts,constants,complement,jacobianTwist,
    coordinateScale,Fin.prod_univ_succ]

theorem published_scaled_exact (i:Fin 4) :
    twistProducts i^2*cubicA i=coordinateScale i^4*publishedA i ∧
    twistProducts i^3*cubicB i=coordinateScale i^6*publishedB i := by
  rw [complementary_twist_exact,(published_twist_exact i).1,(published_twist_exact i).2]
  constructor <;> ring

theorem published_nonsingular (i:Fin 4) :
    4*publishedA i^3+27*publishedB i^2≠0 := by
  fin_cases i <;> norm_num [publishedA,publishedB]

theorem source_constant_squareclasses (i:Fin 4) :
    constants i=(∏j:Fin 3,twistClasses (complement i j)) := by
  fin_cases i <;> norm_num [constants,twistClasses,complement,Fin.prod_univ_succ]
end SourceTwistArithmetic318
