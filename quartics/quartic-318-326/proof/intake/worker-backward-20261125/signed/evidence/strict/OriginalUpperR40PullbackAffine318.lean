module
public import OriginalUpperR40PullbackChart318
public import Mathlib.AlgebraicGeometry.Pullbacks
public section
noncomputable section

namespace OriginalUpperR40PullbackAffine318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalUpperR40PullbackChart318 (Pj localRead)
open scoped TensorProduct
universe u

variable {A k C₀ C₁ : Type u} [CommRing A] [CommRing k] [CommRing C₀] [CommRing C₁]
variable [Algebra A k] [Algebra A C₀] [Algebra k C₁]
variable {Y : Scheme.{u}} (p : Y ⟶ Spec (CommRingCat.of A))
variable (j : Spec (CommRingCat.of C₀) ⟶ Y)
variable (hj : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap A C₀)))

abbrev r : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A k))

variable (e : k ⊗[A] C₀ ≃ₐ[k] C₁)

/-- This is the actual field pullback of the original R40 chart,
transported by the explicit affine pushout algebra, not an
independently selected isomorphic component. -/
@[expose] def affineIso :
    Spec (CommRingCat.of C₁) ≅ Pj p (r (A:=A) (k:=k)) j :=
  Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op ≪≫
    (pullbackSpecIso A k C₀).symm ≪≫ (pullback.congrHom rfl hj).symm

theorem affineIso_read :
    (affineIso p j hj e).hom ≫ localRead p (r (A:=A) (k:=k)) j =
      Spec.map (CommRingCat.ofHom
        (e.toRingHom.comp (Algebra.TensorProduct.includeRight (R:=A) (A:=k) (B:=C₀)).toRingHom)) := by
  simp only [affineIso, localRead, Iso.trans_hom, Iso.symm_hom, Category.assoc, pullback.congrHom_inv,
    pullback.lift_snd, Category.comp_id, pullbackSpecIso_inv_snd]
  change Spec.map (CommRingCat.ofHom e.toRingHom) ≫ _ = _
  rw [← Spec.map_comp]
  rfl

end OriginalUpperR40PullbackAffine318

#print axioms OriginalUpperR40PullbackAffine318.affineIso_read
