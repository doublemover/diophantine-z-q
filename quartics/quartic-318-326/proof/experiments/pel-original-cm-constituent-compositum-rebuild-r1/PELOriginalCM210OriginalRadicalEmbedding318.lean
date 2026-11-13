module
public import PELOriginalCM210RadicalGenerators318
public import Mathlib.FieldTheory.Tower
public section
noncomputable section
namespace PELOriginalCM210OriginalRadicalEmbedding318
open PELOriginalCM210RadicalTower318 PELOriginalCM210RadicalGenerators318
open PELOriginalCM210IntegralConjugation318
/-- Embeds the SAME original CM carrier, not an unnamed quadratic copy.
Its theta goes to the product of the four explicitly constructed radicals. -/
@[expose] def originalEmbedding : K→ₐ[ℚ]H :=
  QuadraticAlgebra.lift ⟨originalTheta,by
    simpa [pow_two,Algebra.smul_def,PELInertiaNormalizerData318.discriminant]
      using originalTheta_square⟩
lemma embedding_theta : originalEmbedding thetaK=originalTheta := by
  simp [originalEmbedding,thetaK,QuadraticAlgebra.lift,QuadraticAlgebra.omega]
lemma embedding_coordinates (z : K) : originalEmbedding z=
    algebraMap ℚ H z.re+algebraMap ℚ H z.im*originalTheta := by
  simp [originalEmbedding,QuadraticAlgebra.lift,Algebra.smul_def]
lemma embedding_injective : Function.Injective originalEmbedding := originalEmbedding.injective
instance originalAlgebra : Algebra K H := originalEmbedding.toRingHom.toAlgebra
instance originalTower : IsScalarTower ℚ K H :=
  IsScalarTower.of_algebraMap_eq (fun q => (originalEmbedding.commutes q).symm)
lemma original_algebraMap (z : K) : algebraMap K H z=originalEmbedding z := rfl
lemma relative_degree : Module.finrank K H=8 := by
  letI : FiniteDimensional K H := FiniteDimensional.right ℚ K H
  have ht := Module.finrank_mul_finrank ℚ K H
  rw [PELOriginalCM210NativeSignature318.degree_two,degree_sixteen] at ht
  omega

end PELOriginalCM210OriginalRadicalEmbedding318
