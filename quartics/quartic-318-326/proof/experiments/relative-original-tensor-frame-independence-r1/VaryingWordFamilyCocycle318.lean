module
public import VaryingWordTripleFamilyMaps318
public section
noncomputable section
namespace VaryingWordFamilyCocycle318
open AlgebraicGeometry CategoryTheory
open VaryingWordTripleFamilyMaps318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v u : ι → List A)
local notation "K" x y z => VaryingWordTripleAlgebra318.ring R A ι x y z
local notation "H" x y => VaryingNormalizedWordOverlap318.ring R A ι x y
local notation "I" x y z => VaryingWordTripleFamily318.ideal R A ι x y z

lemma ring_cycle : rotateMap R A ι u w v ≫ rotateMap R A ι v u w ≫ rotateMap R A ι w v u=𝟙 _ := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective z
  change (rotateMap R A ι w v u).hom ((rotateMap R A ι v u w).hom
    ((rotateMap R A ι u w v).hom (Ideal.Quotient.mk (I w v u) z)))=Ideal.Quotient.mk (I w v u) z
  rw [rotate_mk,rotate_mk,rotate_mk]
  apply congrArg (Ideal.Quotient.mk (I w v u))
  have h := congrArg (fun f : K w v u →ₐ[R] K w v u => Algebra.TensorProduct.map f (AlgHom.id R A))
    (VaryingWordTripleCocycle318.cycle R A ι w v u)
  rw [Algebra.TensorProduct.map_comp_id,Algebra.TensorProduct.map_comp_id,Algebra.TensorProduct.map_id] at h
  exact congrArg (fun f : K w v u ⊗[R] A →ₐ[R] K w v u ⊗[R] A => f z) h

lemma ring_leg : secondMap R A ι v u w ≫ rotateMap R A ι w v u=
    CommRingCat.ofHom (VaryingWordFamilyTransition318.ringEquiv R A ι w v).toRingHom ≫
      firstMap R A ι w v u := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective z
  change (rotateMap R A ι w v u).hom ((secondMap R A ι v u w).hom (Ideal.Quotient.mk _ z))=
    (firstMap R A ι w v u).hom (VaryingWordFamilyTransition318.ringEquiv R A ι w v (Ideal.Quotient.mk _ z))
  rw [second_mk,rotate_mk,VaryingWordFamilyTransition318.ringEquiv_mk,first_mk]
  apply congrArg (Ideal.Quotient.mk (I w v u))
  have h := congrArg (fun f : H v w →ₐ[R] K w v u => Algebra.TensorProduct.map f (AlgHom.id R A))
    (VaryingWordTripleCocycle318.leg R A ι w v u)
  rw [Algebra.TensorProduct.map_comp_id,Algebra.TensorProduct.map_comp_id] at h
  exact congrArg (fun f : H v w ⊗[R] A →ₐ[R] K w v u ⊗[R] A => f z) h

/-- The genuine regular family rotations satisfy the period-three law,
checked on quotient generators of the original tensor source. -/
lemma cycle : rotation R A ι w v u ≫ rotation R A ι v u w ≫ rotation R A ι u w v=𝟙 _ := by
  unfold rotation
  rw [← Spec.map_comp,← Spec.map_comp]
  rw [ring_cycle]
  exact Spec.map_id _
@[reassoc] lemma leg : rotation R A ι w v u ≫ second R A ι v u w=
    first R A ι w v u ≫ (VaryingWordFamilyTransition318.transition R A ι w v).hom := by
  change Spec.map (rotateMap R A ι w v u) ≫ Spec.map (secondMap R A ι v u w)=
    Spec.map (firstMap R A ι w v u) ≫
      Spec.map (CommRingCat.ofHom (VaryingWordFamilyTransition318.ringEquiv R A ι w v).toRingHom)
  rw [← Spec.map_comp,← Spec.map_comp,ring_leg]
end VaryingWordFamilyCocycle318
