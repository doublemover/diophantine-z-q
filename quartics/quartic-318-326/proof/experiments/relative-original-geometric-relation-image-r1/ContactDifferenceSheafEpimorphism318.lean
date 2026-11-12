module
public import ContactDifferenceLocalSurjective318
public section
noncomputable section
namespace ContactDifferenceSheafEpimorphism318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ)
local notation "J" => RelativeFppfLineSheaf318.topology (Spec (CommRingCat.of ℚ))
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
@[expose] def target : Sheaf J (Type 1) :=
  ⟨(RelativeFppfLineSheaf318.sheaf p).obj ⋙ forget CommGrpCat.{1},
    (Presheaf.isSheaf_iff_isSheaf_forget (forget CommGrpCat.{1})).mp (RelativeFppfLineSheaf318.sheaf p).property⟩
@[expose] def source : Sheaf J (Type 1) :=
  (presheafToSheaf J (Type 1)).obj (ContactCartierDifferencePresheaf318.presheaf c)
/-- An actual morphism of sheaves, induced by the SAME original O(D-E)
transformation. No scheme representative of either source or target is inserted. -/
@[expose] def map : source c ⟶ target c :=
  ⟨sheafifyLift J (ContactCartierDifferenceAbel318.transformation c) (target c).property⟩
lemma unit_map : toSheafify J (ContactCartierDifferencePresheaf318.presheaf c) ≫ (map c).hom=
    ContactCartierDifferenceAbel318.transformation c :=
  toSheafify_sheafifyLift J (ContactCartierDifferenceAbel318.transformation c) (target c).property
instance locallySurjective : Sheaf.IsLocallySurjective (map c) :=
  Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (unit_map c)
/-- Genuine epimorphism of associated sheaves from actual bounded
Cartier difference data onto the original relative fppf Picard sheaf.
This does NOT assert representability of a Picard/Jacobian scheme. -/
instance epi : Epi (map c) := Sheaf.epi_of_isLocallySurjective' (map c)
end ContactDifferenceSheafEpimorphism318
