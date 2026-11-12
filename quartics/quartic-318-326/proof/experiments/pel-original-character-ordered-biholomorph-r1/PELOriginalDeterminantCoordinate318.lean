module
public import PELOriginalDeterminantDescent318
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public section
noncomputable section
namespace PELOriginalDeterminantCoordinate318
open QuaternionicRealPeriod318 PELOriginalKernelDeterminantLine318
open PELOriginalKernelMonodromyCovariance318 PELOriginalDeterminantDescent318

/-- The actual universal alternating determinant functional on the true
exterior line, not an unspecified isomorphism between one-dimensional spaces. -/
@[expose] def coefficient : Coordinates →ₗ[ℂ] ℂ :=
  exteriorPower.alternatingMapLinearEquiv
    (Matrix.detRowAlternating : ComplexVectors [⋀^Fin 2]→ₗ[ℂ] ℂ)
@[expose] def generator : Coordinates :=
  exteriorPower.ιMulti ℂ 2 (fun i : Fin 2 => Pi.single i 1)
lemma coefficient_generator : coefficient generator=1 := by
  rw [coefficient,generator,exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  change Matrix.det (fun i j : Fin 2 => Pi.single i (1:ℂ) j)=1
  simp [Matrix.det_fin_two]
lemma generator_ne : generator≠0 := by
  intro h
  have he := coefficient_generator
  rw [h,map_zero] at he
  exact zero_ne_one he
lemma coordinates_rank : Module.finrank ℂ Coordinates=1 := by
  simp [Coordinates,exteriorPower.finrank_eq,QuaternionicRealPeriod318.ComplexVectors]
@[expose] def coordinateEquiv : Coordinates ≃ₗ[ℂ] ℂ where
  toFun := coefficient
  invFun a := a • generator
  left_inv := by
    intro x
    obtain ⟨a,rfl⟩ := (finrank_eq_one_iff_of_nonzero' generator generator_ne).mp
      coordinates_rank x
    rw [map_smul,coefficient_generator,smul_eq_mul,mul_one]
  right_inv := by intro a;rw [map_smul,coefficient_generator,smul_eq_mul,mul_one]
  map_add' := coefficient.map_add
  map_smul' := coefficient.map_smul

@[expose] def transitionMatrix (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => coefficientEquiv u τ hτ (Pi.single i 1) j
@[expose] def transitionScalar (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) : ℂ := (transitionMatrix u τ hτ).det
lemma coefficient_transition_generator (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) :
    coefficient (unitTransition u τ hτ generator)=transitionScalar u τ hτ := by
  change coefficient (exteriorPower.map 2 (coefficientEquiv u τ hτ).toLinearMap
    (exteriorPower.ιMulti ℂ 2 (fun i : Fin 2 => Pi.single i 1)))=_
  rw [exteriorPower.map_apply_ιMulti,coefficient,exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

/-- The scalar transition formula holds for EVERY element of the actual
exterior line and comes from the literal alternating determinant. -/
theorem coefficient_transition (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) (x : Coordinates) :
    coefficient (unitTransition u τ hτ x)=transitionScalar u τ hτ*coefficient x := by
  obtain ⟨a,rfl⟩ := (finrank_eq_one_iff_of_nonzero' generator generator_ne).mp
    coordinates_rank x
  rw [map_smul,map_smul,coefficient_transition_generator,map_smul,coefficient_generator]
  simp only [smul_eq_mul,mul_one]
  ring
lemma transitionScalar_ne (u : PELJointNormOneAction318.normOneUnits)
    (τ : ℂ) (hτ : 0<τ.im) : transitionScalar u τ hτ≠0 := by
  intro h
  have he : coordinateEquiv (unitTransition u τ hτ generator)=coordinateEquiv 0 := by
    change coefficient (unitTransition u τ hτ generator)=coefficient 0
    rw [coefficient_transition_generator,h,map_zero]
  have hv := coordinateEquiv.injective he
  have hz : unitTransition u τ hτ generator=unitTransition u τ hτ 0 := by simpa using hv
  exact generator_ne ((unitTransition u τ hτ).injective hz)
end PELOriginalDeterminantCoordinate318
