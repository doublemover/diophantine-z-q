module
public import SquareZeroUnit318
public import RelativeLineFunctorPullback318
public import PointedLinePullback318
public section
noncomputable section
namespace DualNumberScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R]
abbrev base : Scheme.{u} := Spec (CommRingCat.of R)
abbrev test : Scheme.{u} := Spec (CommRingCat.of (SquareZeroUnit318.Dual R))
@[expose] def reductionRing : SquareZeroUnit318.Dual R →+* R where
  toFun := TrivSqZeroExt.fst
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
@[expose] def structureMap : test R ⟶ base R :=
  Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom R R))
@[expose] def zero : base R ⟶ test R := Spec.map (CommRingCat.ofHom (reductionRing R))
lemma zero_structure : zero R ≫ structureMap R = 𝟙 (base R) := by
  unfold zero structureMap base
  rw [← Spec.map_comp, ← Spec.map_id]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  rfl
variable {X Y : Scheme.{u}} (p : X ⟶ base R) (q : Y ⟶ base R)
abbrev thickening := pullback p (structureMap R)
/-- The actual zero section into the actual dual-number fiber product. -/
@[expose] def reduction : X ⟶ thickening R p :=
  pullback.lift (𝟙 X) (p ≫ zero R) (by simp [Category.assoc, zero_structure])
@[reassoc] lemma reduction_fst : reduction R p ≫ pullback.fst p (structureMap R) = 𝟙 X :=
  pullback.lift_fst _ _ _
@[reassoc] lemma reduction_snd : reduction R p ≫ pullback.snd p (structureMap R) = p ≫ zero R :=
  pullback.lift_snd _ _ _
/-- This is exactly the existing relative-Picard base-change map. -/
abbrev map (f : X ⟶ Y) (hf : f ≫ q = p) : thickening R p ⟶ thickening R q :=
  RelativeLineFunctorPullback318.baseMap p q f hf (structureMap R)
lemma reduction_map (f : X ⟶ Y) (hf : f ≫ q = p) :
    reduction R p ≫ map R p q f hf = f ≫ reduction R q := by
  apply pullback.hom_ext
  · simp only [Category.assoc, map, RelativeLineFunctorPullback318.baseMap_fst,
      reduction_fst, reduction_fst_assoc, Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, map, RelativeLineFunctorPullback318.baseMap_snd,
      reduction_snd, reduction_snd_assoc]
    rw [← Category.assoc, hf]
abbrev Deformation := PointedLineDeformation318.Deformation (reduction R p)
abbrev Class := PointedLineDeformation318.Class (reduction R p)
/-- Actual pointed deformation pullback along the original map, not a map on
an abstract vector space merely assigned the same name. -/
@[expose] def pullback (f : X ⟶ Y) (hf : f ≫ q = p) : Class R q → Class R p :=
  PointedLinePullback318.pullback (reduction R p) (reduction R q)
    (map R p q f hf) f (reduction_map R p q f hf)
lemma forget_pullback (f : X ⟶ Y) (hf : f ≫ q = p) (c : Class R q) :
    PointedLineDeformation318.forget (reduction R p) (pullback R p q f hf c) =
      LineSheafPullback318.pullback (map R p q f hf)
        (PointedLineDeformation318.forget (reduction R q) c) :=
  PointedLinePullback318.forget_pullback _ _ _ _ _ c
end DualNumberScheme318
