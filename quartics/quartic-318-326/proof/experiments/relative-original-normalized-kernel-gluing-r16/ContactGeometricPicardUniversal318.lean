module
public import ContactGeometricPicardDescent318
public section
noncomputable section
namespace ContactGeometricPicardUniversal318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "J" => RelativeFppfLineSheaf318.topology Q
local notation "A" => ContactCartierDifferencePresheaf318.presheaf c
local notation "P" => ContactDifferenceSheafEpimorphism318.target c
variable (F : Sheaf J (Type 1)) (a : A ⟶ F.obj)
  (ha : ContactGeometricIsomInvariant318.Invariant c F a)
/-- Actual Picard-sheaf descent is unique: use the proved Cartier Abel
sheaf epimorphism and native sheafification uniqueness, not assumed
surjectivity on points or a represented quotient. -/
lemma unique (g : P ⟶ F) (hg : ContactCartierDifferenceAbel318.transformation c ≫ g.hom=a) :
    g=ContactGeometricPicardDescent318.descend c F a ha := by
  apply (cancel_epi (ContactDifferenceSheafEpimorphism318.map c)).mp
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ F.property
  change toSheafify J A ≫ ((ContactDifferenceSheafEpimorphism318.map c).hom ≫ g.hom)=
    toSheafify J A ≫ ((ContactDifferenceSheafEpimorphism318.map c).hom ≫
      (ContactGeometricPicardDescent318.descend c F a ha).hom)
  simp only [←Category.assoc,ContactDifferenceSheafEpimorphism318.unit_map]
  exact hg.trans (ContactGeometricPicardDescent318.factor c F a ha).symm
/-- Geometric coequalization criterion for the original varying Picard
SHEAF: test the produced universal Isom schemes over affine coefficients,
and obtain ONE unique map out of the actual Picard sheaf on the whole site.
This theorem neither assumes nor asserts scheme representability. -/
lemma iff_unique_descent : ContactGeometricIsomInvariant318.Invariant c F a ↔
    ∃! g : P ⟶ F, ContactCartierDifferenceAbel318.transformation c ≫ g.hom=a := by
  constructor
  · intro h
    exact ⟨ContactGeometricPicardDescent318.descend c F a h,
      ContactGeometricPicardDescent318.factor c F a h,fun g hg => unique c F a h g hg⟩
  · rintro ⟨g,hg,_⟩
    exact ContactAbelUniversalIsomInvariant318.of_factor c F a g hg
end ContactGeometricPicardUniversal318
