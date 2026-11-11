module
public import ContactProjectiveClassifiedBaseChange318
public section
noncomputable section
namespace ContactHilbertBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S T : CommRingCat.{0}) [Algebra ℚ S] [Algebra ℚ T]
  (φ : S →ₐ[ℚ] T) (D : ContactHilbertData318.FixedRank S c n)
/-- STANDARD quotient coefficient change is the actual full ideal
comap; finite-flat/FP and rank are proved via the equivalent independent
local condition, not by transporting a parameter-point definition. -/
@[expose] def map : ContactHilbertData318.FixedRank T c n :=
  ContactHilbertIdealCharacterization318.fromClassified c n T
    (ContactProjectiveClassifiedBaseChange318.map c n S T φ
      (ContactHilbertIdealCharacterization318.toClassified c n S D))
lemma ideal_map : (map c n S T φ D).val.ideal=D.val.ideal.comap
    (RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S T φ (ContactIntrinsicDifferentials318.structureMap c)) := rfl
lemma natural : ContactHilbertFixedRankEquiv318.equivalence c n T (map c n S T φ D)=
    ContactProjectiveParameterPoint318.map c n S T φ (ContactHilbertFixedRankEquiv318.equivalence c n S D) :=
  ContactProjectiveClassifiedBaseChange318.natural c n S T φ
    (ContactHilbertIdealCharacterization318.toClassified c n S D)
lemma coefficient_id : RelativeCoefficientChange318.familyMap (CommRingCat.of ℚ) S S (AlgHom.id ℚ S)
    (ContactIntrinsicDifferentials318.structureMap c)=𝟙 _ := by
  apply pullback.hom_ext
  · rw [RelativeCoefficientChange318.familyMap_original,Category.id_comp]
  · rw [RelativeCoefficientChange318.familyMap_test,Category.id_comp]
    change pullback.snd _ _ ≫ Spec.map (𝟙 S)=pullback.snd _ _
    rw [Spec.map_id,Category.comp_id]
lemma map_id : map c n S S (AlgHom.id ℚ S) D=D := by
  apply Subtype.ext
  apply ContactHilbertData318.Datum.ext
  rw [ideal_map,coefficient_id,Scheme.IdealSheafData.comap_id]
variable (U : CommRingCat.{0}) [Algebra ℚ U] (ψ : T →ₐ[ℚ] U)
lemma map_comp : map c n T U ψ (map c n S T φ D)=map c n S U (ψ.comp φ) D := by
  apply Subtype.ext
  apply ContactHilbertData318.Datum.ext
  rw [ideal_map,ideal_map,ideal_map,← Scheme.IdealSheafData.comap_comp,RelativeCoefficientFunctorial318.comp]
end ContactHilbertBaseChange318
