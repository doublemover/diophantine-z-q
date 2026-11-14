module
public import ContactPicardIsomOrbitFactorization318
public section
noncomputable section
namespace ContactPicardIsomOrbitUniversal318
open AlgebraicGeometry CategoryTheory Opposite
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
local notation "Q" => Spec (CommRingCat.of ℚ)
local notation "J" => RelativeFppfLineSheaf318.topology Q
local notation "B" => Over.mk (baseMap R)
variable (D E : (ContactCartierDifferencePresheaf318.presheaf c).obj (op B))
local notation "L" => ContactDifferenceNaiveClass318.line c B D
local notation "K" => ContactDifferenceNaiveClass318.line c B E
local notation "P" => ContactRelationProjectionImage318.object R c L K
local notation "Y" => yoneda.obj P
local notation "O" => ContactPicardIsomOrbitPresheaf318.presheaf R c D E
local notation "φ" => ContactOriginalPicardDiagonalImage318.relationMap R c D E
variable (F : Sheaf J (Type 1)) (a : Y ⟶ F.obj)
def Invariant : Prop := ∀ (T : Over Q) (z w : T ⟶ P),
  ContactOriginalIsomOrbitRelation318.Related R c L K T z w → a.app (op T) z=a.app (op T) w
variable (ha : Invariant R c D E F a)
def presheafLift : O ⟶ F.obj := WholeMorphismOrbitDescent318.lift φ a
  (fun T z w h => ha T.unop z w ((ContactPicardIsomOrbitPresheaf318.relation_eq_iff R c D E T.unop z w).mp h))
def lift : ContactPicardIsomOrbitSheaf318.sheaf R c D E ⟶ F :=
  ⟨sheafifyLift J (presheafLift R c D E F a ha) F.property⟩
lemma unit_lift : toSheafify J O ≫ (lift R c D E F a ha).hom=presheafLift R c D E F a ha :=
  toSheafify_sheafifyLift J _ _
lemma factor : ContactPicardIsomOrbitFactorization318.transformation R c D E ≫
    (lift R c D E F a ha).hom=a := by
  change (ContactPicardIsomOrbitPresheaf318.quotient R c D E ≫ toSheafify J O) ≫ _=_
  rw [Category.assoc,unit_lift]
  rfl
lemma unique (g : ContactPicardIsomOrbitSheaf318.sheaf R c D E ⟶ F)
    (hg : ContactPicardIsomOrbitFactorization318.transformation R c D E ≫ g.hom=a) :
    g=lift R c D E F a ha := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext J _ _ F.property
  rw [unit_lift]
  exact WholeMorphismOrbitDescent318.unique φ a _ (toSheafify J O ≫ g.hom)
    (by simpa only [ContactPicardIsomOrbitFactorization318.transformation,Category.assoc] using hg)
/-- Effective orbit descent in Type-valued fppf sheaves, with the
relation supplied by actual original automorphism points. This is not
geometric effectivity of a scheme/algebraic-space Picard quotient. -/
lemma iff_unique_descent : Invariant R c D E F a ↔
    ∃! g : ContactPicardIsomOrbitSheaf318.sheaf R c D E ⟶ F,
      ContactPicardIsomOrbitFactorization318.transformation R c D E ≫ g.hom=a := by
  constructor
  · intro h
    exact ⟨lift R c D E F a h,factor R c D E F a h,fun g hg => unique R c D E F a h g hg⟩
  · rintro ⟨g,hg,_⟩ T z w h
    have hq := (ContactPicardIsomOrbitPresheaf318.quotient_eq_iff_orbit R c D E T z w).mpr h
    have hz := ConcreteCategory.congr_hom (congrArg (fun k => k.app (op T)) hg) z
    have hw := ConcreteCategory.congr_hom (congrArg (fun k => k.app (op T)) hg) w
    exact hz.symm.trans ((congrArg (fun q => g.hom.app (op T) ((toSheafify J O).app (op T) q)) hq).trans hw)
end ContactPicardIsomOrbitUniversal318
