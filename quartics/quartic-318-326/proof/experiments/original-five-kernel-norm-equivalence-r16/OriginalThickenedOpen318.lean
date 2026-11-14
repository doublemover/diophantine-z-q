module
public import OriginalAffineLogarithmNaturality318
public import OpenPullbackStructure318
public section
noncomputable section
namespace OriginalThickenedOpen318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open DualNumberScheme318
universe u
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type u) [CommRing R] {X : Scheme.{u}} (p : X ⟶ base R) (U : X.Opens)
abbrev localBase : U.toScheme ⟶ base R := U.ι ≫ p
abbrev Local := thickening R (localBase R p U)
/-- The already-defined original base-changed open inclusion. -/
@[expose] def inclusion : Local R p U ⟶ thickening R p :=
  map R (localBase R p U) p U.ι rfl
lemma inclusion_fst : inclusion R p U ≫ pullback.fst p (structureMap R) =
    pullback.fst (localBase R p U) (structureMap R) ≫ U.ι :=
  RelativeLineFunctorPullback318.baseMap_fst (localBase R p U) p U.ι rfl (structureMap R)
lemma inclusion_snd : inclusion R p U ≫ pullback.snd p (structureMap R) =
    pullback.snd (localBase R p U) (structureMap R) :=
  RelativeLineFunctorPullback318.baseMap_snd (localBase R p U) p U.ι rfl (structureMap R)
lemma inclusion_eq_map : inclusion R p U =
    pullback.map (localBase R p U) (structureMap R) p (structureMap R)
      U.ι (𝟙 _) (𝟙 _) (by simp [localBase]) (by simp) := by
  apply pullback.hom_ext <;>
    simp [inclusion, DualNumberScheme318.map, RelativeLineFunctorPullback318.baseMap]
instance inclusion_open : IsOpenImmersion (inclusion R p U) := by
  rw [inclusion_eq_map]
  infer_instance
/-- Exact original open pullback square, proved by cancellation against the
original defining thickening square. -/
lemma square : IsPullback (pullback.fst (localBase R p U) (structureMap R))
    (inclusion R p U) U.ι (pullback.fst p (structureMap R)) := by
  apply IsPullback.flip
  refine IsPullback.of_right ?_ (inclusion_fst R p U) (IsPullback.of_hasPullback p (structureMap R)).flip
  rw [inclusion_snd]
  exact (IsPullback.of_hasPullback (localBase R p U) (structureMap R)).flip
lemma image : inclusion R p U ''ᵁ ⊤ = (pullback.fst p (structureMap R)) ⁻¹ᵁ U := by
  have h := OpenPullbackStructure318.opens_eq
    (pullback.fst (localBase R p U) (structureMap R)) (inclusion R p U) U.ι
    (pullback.fst p (structureMap R)) (square R p U) ⊤
  simpa only [Scheme.Hom.preimage_top, Scheme.Opens.ι_image_top] using h
abbrev fullOpen : (thickening R p).Opens := (inclusion R p U).opensRange
lemma fullOpen_eq : fullOpen R p U = (pullback.fst p (structureMap R)) ⁻¹ᵁ U := by
  change (inclusion R p U).opensRange = _
  rw [← Scheme.Hom.image_top_eq_opensRange]
  exact image R p U
@[expose] def openIso : Local R p U ≅ (fullOpen R p U).toScheme :=
  (inclusion R p U).isoOpensRange
@[reassoc] lemma openIso_hom_ι : (openIso R p U).hom ≫ (fullOpen R p U).ι = inclusion R p U :=
  Scheme.Hom.isoOpensRange_hom_ι _
@[reassoc] lemma openIso_inv_inclusion : (openIso R p U).inv ≫ inclusion R p U = (fullOpen R p U).ι :=
  Scheme.Hom.isoOpensRange_inv_comp _
@[expose] def localZero : U.toScheme ⟶ (fullOpen R p U).toScheme :=
  reduction R (localBase R p U) ≫ (openIso R p U).hom
@[expose] def localProjection : (fullOpen R p U).toScheme ⟶ U.toScheme :=
  (openIso R p U).inv ≫ pullback.fst (localBase R p U) (structureMap R)
lemma zero_projection : localZero R p U ≫ localProjection R p U = 𝟙 _ := by
  simp [localZero, localProjection, Category.assoc, reduction_fst]
lemma zero_square : localZero R p U ≫ (fullOpen R p U).ι = U.ι ≫ reduction R p := by
  rw [localZero, Category.assoc, openIso_hom_ι]
  exact reduction_map R (localBase R p U) p U.ι rfl
end OriginalThickenedOpen318
