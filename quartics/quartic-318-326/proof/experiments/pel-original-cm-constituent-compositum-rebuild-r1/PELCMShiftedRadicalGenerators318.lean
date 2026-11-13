module
public import PELCMQuadraticConstituentOrders318
public import PELOriginalCM210RadicalGeneration318
public section
noncomputable section
namespace PELCMShiftedRadicalGenerators318
open PELCMQuadraticConstituentFields318
open PELOriginalCM210RadicalTower318 PELOriginalCM210RadicalGenerators318
/-- These are the integral quadratic generators, not the four raw radicals. -/
@[expose] def shifted : Fin 4 → H :=
  ![generator 0, (1 + generator 1) / 2, (1 + generator 2) / 2,
    (1 + generator 3) / 2]
lemma shifted_equation (i : Fin 4) :
    shifted i ^ 2 = algebraMap ℚ H (a i : ℚ) +
      algebraMap ℚ H (b i : ℚ) * shifted i := by
  fin_cases i
  · simpa [shifted, a, b, PELOriginalCM210PrimeDiscriminantData318.radicand]
      using generator_square 0
  · have hs := generator_square 1
    norm_num [shifted, a, b, PELOriginalCM210PrimeDiscriminantData318.radicand] at hs ⊢
    linear_combination (1 / 4 : H) * hs
  · have hs := generator_square 2
    norm_num [shifted, a, b, PELOriginalCM210PrimeDiscriminantData318.radicand] at hs ⊢
    linear_combination (1 / 4 : H) * hs
  · have hs := generator_square 3
    norm_num [shifted, a, b, PELOriginalCM210PrimeDiscriminantData318.radicand] at hs ⊢
    linear_combination (1 / 4 : H) * hs
lemma radical_from_shifted (i : Fin 4) :
    generator i = if i = 0 then shifted i else 2 * shifted i - 1 := by
  fin_cases i <;> norm_num [shifted] <;> ring
lemma radicals_mem (S : Subalgebra ℚ H) (h : ∀ i, shifted i ∈ S) :
    ∀ i, generator i ∈ S := by
  intro i
  rw [radical_from_shifted]
  split_ifs with hi
  · exact h i
  · have htwo : (2 : H) ∈ S := by simpa using S.algebraMap_mem (2 : ℚ)
    exact S.sub_mem (S.mul_mem htwo (h i)) S.one_mem
lemma shifted_generate (S : Subalgebra ℚ H) (h : ∀ i, shifted i ∈ S) : S = ⊤ := by
  apply top_unique
  intro z hz
  exact PELOriginalCM210RadicalGeneration318.all_mem S (radicals_mem S h) z
lemma adjoin_shifted : Algebra.adjoin ℚ (Set.range shifted) = ⊤ :=
  shifted_generate _ (fun i => Algebra.subset_adjoin ⟨i, rfl⟩)
end PELCMShiftedRadicalGenerators318
