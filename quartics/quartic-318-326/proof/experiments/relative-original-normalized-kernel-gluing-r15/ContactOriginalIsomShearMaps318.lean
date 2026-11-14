module
public import ContactOriginalIsomPointTorsor318
public section
noncomputable section
namespace ContactOriginalIsomShearMaps318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ)
  (L K : Line (curve R c))
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c
abbrev source := ContactIsomParameterProduct318.parameter R c L L L K
abbrev target := ContactIsomParameterProduct318.parameter R c L K L K
/-- Literal geometric shear (a,z) maps to (a composed with z,z), using
the already constructed original composition morphism. -/
@[expose] def shear : source R c L K ⟶ target R c L K :=
  pullback.lift (ContactOriginalIsomGeometricComposition318.composition R c L L K)
    (pullback.snd (q L L) (q L K))
    ((ContactOriginalIsomGeometricComposition318.composition_over R c L L K).trans pullback.condition)
lemma shear_fst : shear R c L K ≫ pullback.fst (q L K) (q L K)=
    ContactOriginalIsomGeometricComposition318.composition R c L L K := pullback.lift_fst _ _ _
lemma shear_snd : shear R c L K ≫ pullback.snd (q L K) (q L K)=
    pullback.snd (q L L) (q L K) := pullback.lift_snd _ _ _
/-- The actual pair (z,w inverse) used to recover the full automorphism. -/
@[expose] def differenceMap : target R c L K ⟶
    ContactOriginalIsomGeometricComposition318.pairs R c L K L :=
  pullback.lift (pullback.fst (q L K) (q L K))
    (pullback.snd (q L K) (q L K) ≫ ContactOriginalIsomGeometricInverse318.inversion R c L K)
    (by rw [Category.assoc,ContactOriginalIsomGeometricInverse318.inversion_over]; exact pullback.condition)
lemma difference_fst : differenceMap R c L K ≫ pullback.fst (q L K) (q K L)=
    pullback.fst (q L K) (q L K) := pullback.lift_fst _ _ _
lemma difference_snd : differenceMap R c L K ≫ pullback.snd (q L K) (q K L)=
    pullback.snd (q L K) (q L K) ≫ ContactOriginalIsomGeometricInverse318.inversion R c L K :=
  pullback.lift_snd _ _ _
@[expose] def difference : target R c L K ⟶ ContactGeometricIsomRelationWitness318.parameter R c L L :=
  differenceMap R c L K ≫ ContactOriginalIsomGeometricComposition318.composition R c L K L
lemma difference_base : difference R c L K ≫ q L L=
    pullback.fst (q L K) (q L K) ≫ q L K := by
  rw [difference,Category.assoc,ContactOriginalIsomGeometricComposition318.composition_over]
  change differenceMap R c L K ≫ (pullback.fst (q L K) (q K L) ≫ q L K)=_
  rw [←Category.assoc,difference_fst]
@[expose] def unshear : target R c L K ⟶ source R c L K :=
  pullback.lift (difference R c L K) (pullback.snd (q L K) (q L K))
    ((difference_base R c L K).trans pullback.condition)
lemma unshear_fst : unshear R c L K ≫ pullback.fst (q L L) (q L K)=difference R c L K :=
  pullback.lift_fst _ _ _
lemma unshear_snd : unshear R c L K ≫ pullback.snd (q L L) (q L K)=
    pullback.snd (q L K) (q L K) := pullback.lift_snd _ _ _
end ContactOriginalIsomShearMaps318
