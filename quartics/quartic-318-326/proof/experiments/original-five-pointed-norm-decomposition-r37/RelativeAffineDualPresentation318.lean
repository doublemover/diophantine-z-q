module
public import DualNumberScalarExtension318
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section
namespace RelativeAffineDualPresentation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
abbrev baseMap : DualNumberScheme318.base S ⟶ DualNumberScheme318.base R :=
  Spec.map (CommRingCat.ofHom (algebraMap R S))
abbrev Thick := DualNumberScheme318.thickening R (baseMap R S)
abbrev Tensor := DualNumberScalarExtension318.Tensor R S
/-- This is the original categorical fiber product, not a replacement affine model. -/
@[expose] def affineIso : Thick R S ≅ Spec (CommRingCat.of (Tensor R S)) :=
  pullbackSpecIso R S (DualNumber R)
@[reassoc] lemma affineIso_inv_fst :
    (affineIso R S).inv ≫ pullback.fst (baseMap R S) (DualNumberScheme318.structureMap R) =
      Spec.map (CommRingCat.ofHom (DualNumberScalarExtension318.sectionMap R S)) :=
  pullbackSpecIso_inv_fst R S (DualNumber R)
@[reassoc] lemma affineIso_inv_snd :
    (affineIso R S).inv ≫ pullback.snd (baseMap R S) (DualNumberScheme318.structureMap R) =
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : DualNumber R →ₐ[R] Tensor R S).toRingHom) :=
  pullbackSpecIso_inv_snd R S (DualNumber R)
/-- The ACTUAL zero section, compared to the literal tensor augmentation. -/
lemma reduction_affineIso_inv :
    Spec.map (CommRingCat.ofHom (DualNumberScalarExtension318.reduction R S)) ≫
      (affineIso R S).inv = DualNumberScheme318.reduction R (baseMap R S) := by
  apply pullback.hom_ext
  · rw [Category.assoc, affineIso_inv_fst, DualNumberScheme318.reduction_fst,
      ← Spec.map_comp, ← Spec.map_id]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    exact DualNumberScalarExtension318.reduction_section R S s
  · rw [Category.assoc, affineIso_inv_snd, DualNumberScheme318.reduction_snd]
    change Spec.map (CommRingCat.ofHom (DualNumberScalarExtension318.reduction R S)) ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : DualNumber R →ₐ[R] Tensor R S).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫
        Spec.map (CommRingCat.ofHom (DualNumberScheme318.reductionRing R))
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro d
    exact DualNumberScalarExtension318.reduction_right R S d
lemma reduction_affineIso :
    DualNumberScheme318.reduction R (baseMap R S) ≫ (affineIso R S).hom =
      Spec.map (CommRingCat.ofHom (DualNumberScalarExtension318.reduction R S)) := by
  rw [← reduction_affineIso_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id]
end RelativeAffineDualPresentation318
