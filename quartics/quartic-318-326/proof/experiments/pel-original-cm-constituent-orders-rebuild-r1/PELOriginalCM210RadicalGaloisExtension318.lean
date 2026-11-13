module
public import PELOriginalCM210RadicalSplittingField318
public import Mathlib.FieldTheory.Galois.Basic
public section
noncomputable section
namespace PELOriginalCM210RadicalGaloisExtension318
open PELOriginalCM210RadicalTower318 PELOriginalCM210RadicalSplittingField318
open PELOriginalCM210OriginalRadicalEmbedding318 PELOriginalCM210IntegralConjugation318
instance : Normal ℚ H := Normal.of_isSplittingField polynomial
instance : IsGalois ℚ H where
instance : IsGalois K H := IsGalois.tower_top_of_isGalois ℚ K H
lemma rational_automorphism_card : Nat.card (H≃ₐ[ℚ]H)=16 := by
  rw [IsGalois.card_aut_eq_finrank,degree_sixteen]
lemma original_relative_automorphism_card : Nat.card (H≃ₐ[K]H)=8 := by
  letI : FiniteDimensional K H := FiniteDimensional.right ℚ K H
  rw [IsGalois.card_aut_eq_finrank,relative_degree]
/-- These are actual automorphism groups of the constructed fields.
No class-group/Artin map or unramifiedness is asserted here. -/
lemma relative_degree_and_card :
    Module.finrank K H=8 ∧ Nat.card (H≃ₐ[K]H)=8 :=
  ⟨relative_degree,original_relative_automorphism_card⟩
end PELOriginalCM210RadicalGaloisExtension318
