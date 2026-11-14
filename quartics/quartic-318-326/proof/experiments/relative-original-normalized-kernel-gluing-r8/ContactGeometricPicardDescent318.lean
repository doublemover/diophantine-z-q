module
public import ContactGeometricQuotientLift318
public section
noncomputable section
namespace ContactGeometricPicardDescent318
open AlgebraicGeometry CategoryTheory
variable (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "J" => RelativeFppfLineSheaf318.topology Q
local notation "A" => ContactCartierDifferencePresheaf318.presheaf c
local notation "V" => ContactDifferenceQuotientPresheaf318.presheaf c
local notation "P" => ContactDifferenceSheafEpimorphism318.target c
variable (F : Sheaf J (Type 1)) (a : A ⟶ F.obj)
  (ha : ContactGeometricIsomInvariant318.Invariant c F a)
@[expose] def quotientLift : ContactDifferenceQuotientSheaf318.source c ⟶ F :=
  ⟨sheafifyLift J (ContactGeometricQuotientLift318.lift c F a ha) F.property⟩
lemma unit_quotientLift : toSheafify J V ≫ (quotientLift c F a ha).hom=
    ContactGeometricQuotientLift318.lift c F a ha :=
  toSheafify_sheafifyLift J (ContactGeometricQuotientLift318.lift c F a ha) F.property
/-- Descend to the SAME original relative fppf Picard sheaf through its
proved quotient-sheaf comparison, not a newly named representing scheme. -/
@[expose] def descend : P ⟶ F :=
  (ContactDifferenceQuotientSheaf318.equivalence c).inv ≫ quotientLift c F a ha
lemma comparison_inverse : ContactDifferenceQuotientComparison318.transformation c ≫
    (ContactDifferenceQuotientSheaf318.equivalence c).inv.hom=toSheafify J V := by
  rw [←ContactDifferenceQuotientSheaf318.unit_map]
  change (toSheafify J V ≫ (ContactDifferenceQuotientSheaf318.equivalence c).hom.hom) ≫
    (ContactDifferenceQuotientSheaf318.equivalence c).inv.hom=_
  have hi := congrArg (fun f => f.hom) (ContactDifferenceQuotientSheaf318.equivalence c).hom_inv_id
  change (ContactDifferenceQuotientSheaf318.equivalence c).hom.hom ≫
    (ContactDifferenceQuotientSheaf318.equivalence c).inv.hom=𝟙 _ at hi
  rw [Category.assoc,hi,Category.comp_id]
/-- The descended map agrees with the ORIGINAL all-bound Cartier Abel
transformation on every test and every actual full divisor-difference datum. -/
lemma factor : ContactCartierDifferenceAbel318.transformation c ≫ (descend c F a ha).hom=a := by
  change ContactCartierDifferenceAbel318.transformation c ≫
    ((ContactDifferenceQuotientSheaf318.equivalence c).inv.hom ≫ (quotientLift c F a ha).hom)=a
  rw [←ContactDifferenceQuotientComparison318.factor,Category.assoc,
    ←Category.assoc (ContactDifferenceQuotientComparison318.transformation c),comparison_inverse,
    Category.assoc,unit_quotientLift,ContactGeometricQuotientLift318.factor]
end ContactGeometricPicardDescent318
