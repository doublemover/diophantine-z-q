module
public import LaurentWholeUnitRepresentation318
public section
noncomputable section
namespace ContactOriginalLaurentStabilizer318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c L L
/-- Actual over-base scheme isomorphism from the ORIGINAL stabilizer
onto literal Spec R[t,t⁻¹], obtained from the two exact whole-test classifiers. -/
@[expose] def overIso : Over.mk q ≅ Over.mk (LaurentWholeUnitRepresentation318.projection R) :=
  Yoneda.fullyFaithful.preimageIso
    (ContactOriginalStabilizerUnitPresheaf318.representation R c L ≪≫
      (LaurentWholeUnitRepresentation318.representation R).symm)
@[expose] def schemeIso : ContactGeometricIsomRelationWitness318.parameter R c L L ≅
    LaurentWholeUnitRepresentation318.scheme R :=
  (Over.forget (Spec R)).mapIso (overIso R c L)
@[reassoc] lemma hom_base : (schemeIso R c L).hom ≫
    LaurentWholeUnitRepresentation318.projection R=q := (overIso R c L).hom.w
@[reassoc] lemma inv_base : (schemeIso R c L).inv ≫ q=
    LaurentWholeUnitRepresentation318.projection R := (overIso R c L).inv.w

end ContactOriginalLaurentStabilizer318
