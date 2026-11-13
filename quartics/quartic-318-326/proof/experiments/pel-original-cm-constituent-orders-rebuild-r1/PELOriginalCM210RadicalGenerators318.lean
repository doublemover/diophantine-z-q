module
public import PELOriginalCM210RadicalTower318
public section
noncomputable section
namespace PELOriginalCM210RadicalGenerators318
open PELOriginalCM210RadicalTower318 PELOriginalCM210PrimeDiscriminantData318
@[expose] def generator : Fin 4→H := ![algebraMap First H QuadraticAlgebra.omega,
  algebraMap Second H QuadraticAlgebra.omega,algebraMap Third H QuadraticAlgebra.omega,
  QuadraticAlgebra.omega]
lemma generator_square (i : Fin 4) : generator i^2=algebraMap ℚ H (radicand i) := by
  fin_cases i <;> simp [generator,radicand,←map_pow,QuadraticAlgebra.omega_pow_two_eq_add,
    Algebra.smul_def,←IsScalarTower.algebraMap_apply]
@[expose] def originalTheta : H := ((generator 0*generator 1)*generator 2)*generator 3
lemma originalTheta_square : originalTheta^2=algebraMap ℚ H (-210) := by
  simp only [originalTheta,mul_pow,generator_square,←map_mul,radicand_product]
lemma generator_nonzero (i : Fin 4) : generator i≠0 := by
  intro h
  have hs := generator_square i
  rw [h,zero_pow (by decide)] at hs
  fin_cases i <;> norm_num [radicand] at hs

end PELOriginalCM210RadicalGenerators318
