module
public import OriginalDualSectionLift318
public section
noncomputable section
namespace OriginalAffineDualSections318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RelativeAffineDualPresentation318
open scoped TensorProduct
universe u
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
/-- Coordinates are the ACTUAL inverse comparison on global sections followed
by the original Gamma-Spec isomorphism, not a chosen abstract ring model. -/
@[expose] def coordinates : Γ(Thick R S,⊤) ≃+* Tensor R S :=
  (Scheme.Γ.mapIso (affineIso R S).symm.op ≪≫
    Scheme.ΓSpecIso (CommRingCat.of (Tensor R S))).commRingCatIsoToRingEquiv
@[expose] def baseCoordinates : Γ(DualNumberScheme318.base S,⊤) ≃+* S :=
  (Scheme.ΓSpecIso (CommRingCat.of S)).commRingCatIsoToRingEquiv
lemma coordinates_first_raw (s : S) :
    coordinates R S ((pullback.fst (baseMap R S) (DualNumberScheme318.structureMap R)).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) = s ⊗ₜ[R] 1 := by
  change (Scheme.ΓSpecIso (CommRingCat.of (Tensor R S))).hom
    (((pullback.fst (baseMap R S) (DualNumberScheme318.structureMap R)).appTop ≫
      (affineIso R S).inv.appTop) ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) = _
  rw [← Scheme.Hom.comp_appTop, affineIso_inv_fst]
  have hn := congrArg (fun k => k s) (Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (DualNumberScalarExtension318.sectionMap R S)))
  rw [← hn]
  all_goals exact Iso.inv_hom_id_apply _ _
lemma coordinates_first (s : Γ(DualNumberScheme318.base S,⊤)) :
    coordinates R S ((pullback.fst (baseMap R S) (DualNumberScheme318.structureMap R)).appTop s) =
      baseCoordinates S s ⊗ₜ[R] 1 := by
  have h := coordinates_first_raw R S (baseCoordinates S s)
  change coordinates R S ((pullback.fst (baseMap R S) (DualNumberScheme318.structureMap R)).appTop
    ((Scheme.ΓSpecIso (CommRingCat.of S)).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).hom s))) = _ at h
  rw [Iso.hom_inv_id_apply] at h
  exact h
lemma coordinates_epsilon :
    coordinates R S (DualNumberInfinitesimalLines318.epsilon R (baseMap R S)) =
      DualNumberScalarExtension318.epsilon R S := by
  change (Scheme.ΓSpecIso (CommRingCat.of (Tensor R S))).hom
    (((pullback.snd (baseMap R S) (DualNumberScheme318.structureMap R)).appTop ≫
      (affineIso R S).inv.appTop)
      ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber R))).inv DualNumber.eps)) = _
  rw [← Scheme.Hom.comp_appTop, affineIso_inv_snd]
  have hn := congrArg (fun k => k (DualNumber.eps : DualNumber R))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : DualNumber R →ₐ[R] Tensor R S).toRingHom))
  rw [← hn]
  all_goals exact Iso.inv_hom_id_apply _ _
/-- The original canonical section lift agrees with the actual affine tensor
inverse on every coefficient pair, fixing BOTH projections and epsilon. -/
lemma coordinates_lift (x : SquareZeroUnit318.Dual Γ(DualNumberScheme318.base S,⊤)) :
    coordinates R S (OriginalDualSectionLift318.lift R (baseMap R S) x) =
      (DualNumberScalarExtension318.equivalence R S).symm
        (SquareZeroRingLift318.congr (baseCoordinates S) x) := by
  change coordinates R S
    ((pullback.fst (baseMap R S) (DualNumberScheme318.structureMap R)).appTop x.fst +
      DualNumberInfinitesimalLines318.epsilon R (baseMap R S) *
        (pullback.fst (baseMap R S) (DualNumberScheme318.structureMap R)).appTop x.snd) = _
  rw [map_add, map_mul, coordinates_first, coordinates_first, coordinates_epsilon]
  change _ = DualNumberScalarExtension318.backward R S
    (SquareZeroUnit318.map _ (baseCoordinates S).toRingHom x)
  simp only [DualNumberScalarExtension318.backward, DualNumber.lift_apply_apply,
    SquareZeroUnit318.map_fst, SquareZeroUnit318.map_snd,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]
  exact congrArg (fun z => (baseCoordinates S x.fst ⊗ₜ[R] 1) + z) (mul_comm _ _)
lemma lift_bijective : Function.Bijective (OriginalDualSectionLift318.lift R (baseMap R S)) := by
  let e := (SquareZeroRingLift318.congr (baseCoordinates S)).trans
    ((DualNumberScalarExtension318.equivalence R S).symm.toRingEquiv.trans (coordinates R S).symm)
  have h : (OriginalDualSectionLift318.lift R (baseMap R S) : _ → _) = e := by
    funext x
    apply (coordinates R S).injective
    rw [coordinates_lift]
    exact ((coordinates R S).apply_symm_apply _).symm
  rw [h]
  exact e.bijective
end OriginalAffineDualSections318
