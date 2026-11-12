module
public import WholeSchemeFiberParameterPoints318
public section
noncomputable section
namespace ContactOriginalIsomBaseChangedParameter318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318 ContactWholeIsomNaturality318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K : Line (curve R c)) {T : Scheme.{0}} (t : T ⟶ Spec R)
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c L K
/-- Literal pullback of the SAME original parameter to an arbitrary,
possibly nonaffine/nonreduced coefficient scheme. -/
abbrev parameter := pullback q t
@[expose] def projection : parameter R c L K t ⟶ T := pullback.snd q t
variable {S : Scheme.{0}} (s : S ⟶ T)
abbrev Points := {z : S ⟶ parameter R c L K t // z ≫ projection R c L K t=s}
/-- Full original Isom classification after arbitrary whole base change;
the original curve and coefficient family are not replaced by a surrogate. -/
@[expose] def equivalence : Points R c L K t s ≃ ContactWholeIsomNaturality318.Isoms R c L K (s ≫ t) :=
  (WholeSchemeFiberParameterPoints318.equivalence q t s).trans
    (ContactWholeIsomPointEquivalence318.equivalence R c L K S (s ≫ t))
@[expose] def classify (e : ContactWholeIsomNaturality318.Isoms R c L K (s ≫ t)) :
    Points R c L K t s := (equivalence R c L K t s).symm e
lemma classify_fst (e : ContactWholeIsomNaturality318.Isoms R c L K (s ≫ t)) :
    (classify R c L K t s e).val ≫ pullback.fst q t=
      (ContactGeometricIsomRelationWitness318.pointOfIso R c L K S (s ≫ t) e).val :=
  pullback.lift_fst _ _ _
lemma classify_snd (e : ContactWholeIsomNaturality318.Isoms R c L K (s ≫ t)) :
    (classify R c L K t s e).val ≫ pullback.snd q t=s :=
  (classify R c L K t s e).property
end ContactOriginalIsomBaseChangedParameter318
