module
public import RelativeAffinePointedTriviality318
public section
noncomputable section
namespace DualThickeningIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X Y : Scheme.{u}}
    (p : X ⟶ DualNumberScheme318.base R) (q : Y ⟶ DualNumberScheme318.base R)
    (e : X ≅ Y) (he : e.hom ≫ q = p)
include he in
lemma inverse_over : e.inv ≫ p = q := by rw [← he, Iso.inv_hom_id_assoc]
/-- Actual base change of the original scheme isomorphism, with both inverses
and both original fiber-product projections checked. -/
@[expose] def iso : DualNumberScheme318.thickening R p ≅ DualNumberScheme318.thickening R q where
  hom := DualNumberScheme318.map R p q e.hom he
  inv := DualNumberScheme318.map R q p e.inv (inverse_over R p q e he)
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp [DualNumberScheme318.map, RelativeLineFunctorPullback318.baseMap, Category.assoc]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp [DualNumberScheme318.map, RelativeLineFunctorPullback318.baseMap, Category.assoc]
lemma reduction_hom : DualNumberScheme318.reduction R p ≫ (iso R p q e he).hom =
    e.hom ≫ DualNumberScheme318.reduction R q :=
  DualNumberScheme318.reduction_map R p q e.hom he
lemma reduction_inv : DualNumberScheme318.reduction R q ≫ (iso R p q e he).inv =
    e.inv ≫ DualNumberScheme318.reduction R p :=
  DualNumberScheme318.reduction_map R q p e.inv (inverse_over R p q e he)
variable (L : DualNumberScheme318.Deformation R p)
@[expose] def transport : DualNumberScheme318.Deformation R q :=
  PointedLinePullback318.deformation _ _ (iso R p q e he).inv e.inv (reduction_inv R p q e he) L
/-- Returning an actual frame across the actual comparison, with canonical
unit, composition, equality and identity pullback maps retained. -/
@[expose] def frameOfTransport
    (t : SheafOfModules.unit (DualNumberScheme318.thickening R q).ringCatSheaf ≅
      (transport R p q e he L).line.object) :
    SheafOfModules.unit (DualNumberScheme318.thickening R p).ringCatSheaf ≅ L.line.object :=
  (IdentityCotangent318.pullbackUnitIso (iso R p q e he).hom).symm ≪≫
    (Scheme.Modules.pullback (iso R p q e he).hom).mapIso t ≪≫
    (Scheme.Modules.pullbackComp (iso R p q e he).hom (iso R p q e he).inv).app L.line.object ≪≫
    (Scheme.Modules.pullbackCongr (iso R p q e he).hom_inv_id).app L.line.object ≪≫
    (Scheme.Modules.pullbackId _).app L.line.object
end DualThickeningIso318
