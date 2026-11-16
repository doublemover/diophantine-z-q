module
public import RelativeAmbientReassociation318
public section
noncomputable section
namespace ContactRelativeBoundedLine318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (N : ℕ)
  {B T : Scheme.{0}} (b : B ⟶ Spec R)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
local notation "r" => baseMap R
local notation "q" => ContactRelativeStructuralHOne318.projection R c
@[expose] def line (D : ContactBoundedCartierEquiv318.Data c N (b ≫ r)) : Line (pullback q b) :=
  LineSheafPullback318.line (RelativeAmbientReassociation318.comparison p r b).hom
    (ContactBoundedCartierAbel318.divisorLine c N (b ≫ r) D)
/-- Whole divisor lines of actual bounded Q-families, viewed over the
original affine coefficient base, obey arbitrary coefficient pullback. -/
lemma coefficient (t : T ⟶ Spec R) (j : T ⟶ B) (hj : j ≫ b=t)
    (D : ContactBoundedCartierEquiv318.Data c N (b ≫ r)) :
    classOf (line R c N t (ContactBoundedCartierBaseChange318.map c N (b ≫ r) (t ≫ r)
      j (by rw [←Category.assoc,hj]) D))=
      classOf (LineSheafPullback318.line (RelativeSchemeCoefficient318.map q b t j hj)
        (line R c N b D)) := by
  change LineClassPullbackHom318.pullback (RelativeAmbientReassociation318.comparison p r t).hom
    (classOf (ContactBoundedCartierAbel318.divisorLine c N (t ≫ r) _))=
      LineClassPullbackHom318.pullback (RelativeSchemeCoefficient318.map q b t j hj)
        (LineClassPullbackHom318.pullback (RelativeAmbientReassociation318.comparison p r b).hom _)
  rw [ContactBoundedCartierDivisorChange318.divisor_class]
  change LineClassPullbackHom318.pullback (RelativeAmbientReassociation318.comparison p r t).hom
    (LineClassPullbackHom318.pullback (RelativeSchemeCoefficient318.map p (b ≫ r) (t ≫ r) j _) _)=_
  rw [←MonoidHom.comp_apply,←LineClassPullbackHom318.composition,
    ←MonoidHom.comp_apply,←LineClassPullbackHom318.composition,
    RelativeAmbientReassociation318.natural]
end ContactRelativeBoundedLine318
