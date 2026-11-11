module
public import VaryingWordFamilyTriplePullback318
public section
noncomputable section
namespace VaryingWordFamilySelf318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w : ι → List A)
instance inclusion_self : IsIso (VaryingWordOverlapFamily318.into R A ι w w) := by
  rw [← (VaryingWordOverlapFamily318.cartesian R A ι w w).isoPullback_hom_fst]
  infer_instance
lemma ring_self : CommRingCat.ofHom (VaryingWordFamilyTransition318.ringEquiv R A ι w w).toRingHom=𝟙 _ := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective z
  change VaryingWordFamilyTransition318.ringEquiv R A ι w w (Ideal.Quotient.mk _ z)=Ideal.Quotient.mk _ z
  rw [VaryingWordFamilyTransition318.ringEquiv_mk]
  change Ideal.Quotient.mk _
    (Algebra.TensorProduct.map (VaryingNormalizedOverlapScheme318.transitionRing R A ι w w)
      (AlgHom.id R A) z)=Ideal.Quotient.mk _ z
  rw [VaryingWordOverlapSelf318.transition_ring,Algebra.TensorProduct.map_id,AlgHom.id_apply]
lemma transition_self : (VaryingWordFamilyTransition318.transition R A ι w w).hom=𝟙 _ := by
  change Spec.map (CommRingCat.ofHom (VaryingWordFamilyTransition318.ringEquiv R A ι w w).toRingHom)=_
  rw [ring_self]
  exact Spec.map_id _
end VaryingWordFamilySelf318
