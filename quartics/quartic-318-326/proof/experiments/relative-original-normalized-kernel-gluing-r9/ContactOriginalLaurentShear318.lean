module
public import ContactOriginalSmoothStabilizer318
public import PullbackSourceIso318
public section
noncomputable section
namespace ContactOriginalLaurentShear318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits LineSheafClass318
open ContactOriginalRelativePolynomialCharts318
variable (R : CommRingCat.{0}) [Algebra ℚ R] (c : Fin 4 → ℚˣ) (L K : Line (curve R c))
local notation "q" => ContactGeometricIsomRelationWitness318.projection R c
local notation "g" => LaurentWholeUnitRepresentation318.projection R
@[expose] def change : pullback (q L L) (q L K) ≅ pullback g (q L K) :=
  PullbackSourceIso318.iso (q L L) g (q L K)
    (ContactOriginalLaurentStabilizer318.schemeIso R c L)
    (ContactOriginalLaurentStabilizer318.hom_base R c L)
/-- Actual Laurent-Gm shear isomorphism on the SAME original Isom
parameter. This includes the complete scheme structure, not merely points. -/
@[expose] def shear : pullback g (q L K) ≅ pullback (q L K) (q L K) :=
  (change R c L K).symm ≪≫ ContactOriginalIsomTorsorOver318.schemeIso R c L K
@[expose] def action : pullback g (q L K) ⟶ ContactGeometricIsomRelationWitness318.parameter R c L K :=
  (change R c L K).inv ≫ ContactOriginalIsomGeometricComposition318.composition R c L L K
@[reassoc] lemma shear_fst : (shear R c L K).hom ≫ pullback.fst (q L K) (q L K)=action R c L K := by
  change ((change R c L K).inv ≫ ContactOriginalIsomShearMaps318.shear R c L K) ≫ _=_
  rw [Category.assoc,ContactOriginalIsomShearMaps318.shear_fst]
@[reassoc] lemma shear_snd : (shear R c L K).hom ≫ pullback.snd (q L K) (q L K)=pullback.snd g (q L K) := by
  change ((change R c L K).inv ≫ ContactOriginalIsomShearMaps318.shear R c L K) ≫ _=_
  rw [Category.assoc,ContactOriginalIsomShearMaps318.shear_snd]
  exact PullbackSourceIso318.inv_snd _ _ _ _ _
@[reassoc] lemma unshear_snd : (shear R c L K).inv ≫ pullback.snd g (q L K)=pullback.snd (q L K) (q L K) := by
  rw [←shear_snd R c L K,Iso.inv_hom_id_assoc]
/-- Over-Isom version: the self-pullback is LITERALLY the trivial
Laurent group bundle over the original Isom parameter. -/
@[expose] def overIso : Over.mk (pullback.snd g (q L K)) ≅
    Over.mk (pullback.snd (q L K) (q L K)) where
  hom := Over.homMk (shear R c L K).hom (shear_snd R c L K)
  inv := Over.homMk (shear R c L K).inv (unshear_snd R c L K)
  hom_inv_id := by apply Over.OverMorphism.ext; exact (shear R c L K).hom_inv_id
  inv_hom_id := by apply Over.OverMorphism.ext; exact (shear R c L K).inv_hom_id

end ContactOriginalLaurentShear318
