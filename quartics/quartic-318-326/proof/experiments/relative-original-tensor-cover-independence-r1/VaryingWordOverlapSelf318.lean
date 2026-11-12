module
public import VaryingWordOverlapIso318
public section
noncomputable section
namespace VaryingWordOverlapSelf318
open VaryingNormalizedWordOverlap318 VaryingNormalizedOverlapFrames318
open AlgebraicGeometry CategoryTheory
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
local notation "N" => VaryingNormalizedWordParameter318.ring R A ι w
local notation "H" => VaryingNormalizedWordOverlap318.ring R A ι w w
lemma delta_one : delta R A ι w w=1 := by
  change (VaryingMatrixWords318.columns (universal R A ι w).val.val w).det=1
  rw [(universal R A ι w).property,Matrix.det_one]

@[expose] def ringIso : N ≃ₐ[N] H :=
  IsLocalization.atUnit N H (delta R A ι w w) (by rw [delta_one]; exact isUnit_one)
lemma ringIso_map : (ringIso R A ι w).toRingHom=algebraMap N H := by
  ext a
  simpa only [Algebra.algebraMap_self_apply] using (ringIso R A ι w).commutes a
@[expose] def schemeIso : VaryingNormalizedOverlapScheme318.overlap R A ι w w ≅
    VaryingNormalizedOverlapScheme318.chart R A ι w :=
  Scheme.Spec.mapIso (ringIso R A ι w).toRingEquiv.toCommRingCatIso.op
lemma schemeIso_hom : (schemeIso R A ι w).hom=VaryingNormalizedOverlapScheme318.into R A ι w w := by
  change Spec.map (CommRingCat.ofHom (ringIso R A ι w).toRingHom)=_
  rw [ringIso_map]
  rfl
instance into_iso : IsIso (VaryingNormalizedOverlapScheme318.into R A ι w w) := by
  rw [← schemeIso_hom]
  infer_instance

lemma transition_point (S : Type u) [CommRing S] [Algebra R S]
    (d : Point R A ι w S w) : transition R A ι w S w d=d := by
  apply (overlapFrames R A ι w S w).injective
  change (overlapFrames R A ι w S w)
    ((overlapFrames R A ι w S w).symm
      (CyclicWordFrameOverlap318.transition S (S ⊗[R] A) ι
        (fun j => (1 : S) ⊗ₜ[R] (w j).prod) (fun j => (1 : S) ⊗ₜ[R] (w j).prod)
        (overlapFrames R A ι w S w d)))=_
  rw [Equiv.apply_symm_apply]
  apply Subtype.ext
  apply Subtype.ext
  exact CyclicWordFrameCocycle318.normalization_identity S (S ⊗[R] A) ι
    (overlapFrames R A ι w S w d).val.val (fun j => (1 : S) ⊗ₜ[R] (w j).prod)
    (overlapFrames R A ι w S w d).val.property

lemma transition_ring : VaryingNormalizedOverlapScheme318.transitionRing R A ι w w=AlgHom.id R H := by
  apply (pointsOnOpen R A ι w H w).injective
  rw [VaryingNormalizedOverlapScheme318.transition_universal,transition_point]
lemma transition_self : VaryingNormalizedOverlapScheme318.transition R A ι w w=𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (VaryingNormalizedOverlapScheme318.transitionRing R A ι w w).toRingHom)=_
  rw [transition_ring]
  exact Spec.map_id _
end VaryingWordOverlapSelf318
