module
public import PELOriginalCM210RadicalGeneration318
public import Mathlib.FieldTheory.SplittingField.IsSplittingField
public section
noncomputable section
namespace PELOriginalCM210RadicalSplittingField318
open Polynomial
open PELOriginalCM210PrimeDiscriminantData318 PELOriginalCM210RadicalTower318
open PELOriginalCM210RadicalGenerators318 PELOriginalCM210RadicalGeneration318
@[expose] def factor (i:Fin 4) : ℚ[X] := X^2-C (radicand i)
@[expose] def polynomial : ℚ[X] := ((factor 0*factor 1)*factor 2)*factor 3
lemma factor_monic (i:Fin 4) : (factor i).Monic := monic_X_pow_sub_C _ (by decide)
lemma polynomial_monic : polynomial.Monic :=
  (((factor_monic 0).mul (factor_monic 1)).mul (factor_monic 2)).mul (factor_monic 3)
lemma factor_map (i:Fin 4) :
    (factor i).map (algebraMap ℚ H)=(X-C (generator i))*(X-C (-generator i)) := by
  simp only [factor,Polynomial.map_sub,Polynomial.map_pow,Polynomial.map_X,Polynomial.map_C]
  have hc : (C (generator i):H[X])^2=C (algebraMap ℚ H (radicand i)) := by
    rw [←map_pow,generator_square]
  rw [←hc,map_neg]
  ring
lemma factor_splits (i:Fin 4) : ((factor i).map (algebraMap ℚ H)).Splits := by
  rw [factor_map]
  exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)
lemma polynomial_splits : (polynomial.map (algebraMap ℚ H)).Splits := by
  simp only [polynomial,Polynomial.map_mul]
  exact (((factor_splits 0).mul (factor_splits 1)).mul (factor_splits 2)).mul (factor_splits 3)
lemma generator_root (i:Fin 4) : aeval (generator i) polynomial=0 := by
  fin_cases i <;> simp [polynomial,factor,generator_square,radicand]
lemma full_root_adjoin : Algebra.adjoin ℚ (polynomial.rootSet H:Set H)=⊤ := by
  apply top_unique
  intro z _
  apply all_mem
  intro i
  exact Algebra.subset_adjoin (polynomial_monic.mem_rootSet.mpr (generator_root i))
instance : IsSplittingField ℚ H polynomial := ⟨polynomial_splits,full_root_adjoin⟩
end PELOriginalCM210RadicalSplittingField318
