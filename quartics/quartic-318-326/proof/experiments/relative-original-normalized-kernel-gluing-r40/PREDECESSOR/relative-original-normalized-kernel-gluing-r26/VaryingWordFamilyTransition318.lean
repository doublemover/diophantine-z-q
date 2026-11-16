module
public import VaryingWordOverlapFamily318
public section
noncomputable section
namespace VaryingWordFamilyTransition318
open AlgebraicGeometry CategoryTheory
open VaryingWordOverlapFamily318
open scoped TensorProduct
universe u
variable (R A ι : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [Fintype ι] [DecidableEq ι] (w v : ι → List A)
local notation "H" s t => VaryingNormalizedWordOverlap318.ring R A ι s t
local notation "f" => VaryingNormalizedOverlapScheme318.transitionRing R A ι w v

lemma transition_data : VaryingNormalizedWordNaturality318.mapPoint R A ι v (H v w) (H w v) f
    (data R A ι v w)=
      (VaryingNormalizedOverlapFrames318.transition R A ι w (H w v) v (point R A ι w v)).val := by
  rw [data_point]
  have h := VaryingNormalizedWordOverlap318.toPoint_natural R A ι v (H v w) w (H w v) f
    (AlgHom.id R (H v w))
  simp only [AlgHom.comp_id] at h
  have h' := h.symm.trans (VaryingNormalizedOverlapScheme318.transition_universal R A ι w v)
  exact congrArg Subtype.val h'

@[expose] def sourceEquiv : H v w ⊗[R] A ≃ₐ[R] H w v ⊗[R] A :=
  Algebra.TensorProduct.congr (VaryingWordOverlapIso318.ringEquiv R A ι w v) (AlgEquiv.refl R A)
lemma ideal_map : Ideal.map (sourceEquiv R A ι w v).toRingHom (ideal R A ι v w)=ideal R A ι w v := by
  have h := VaryingNormalizedIdealBaseChange318.ideal_map R A ι v (H v w) (H w v) f (data R A ι v w)
  rw [transition_data,VaryingWordIdealOverlap318.transition_ideal] at h
  rw [← data_point] at h
  exact h
@[expose] def ringEquiv : ring R A ι v w ≃ₐ[R] ring R A ι w v :=
  Ideal.quotientEquivAlg (ideal R A ι v w) (ideal R A ι w v)
    (sourceEquiv R A ι w v) (ideal_map R A ι w v).symm
lemma ringEquiv_mk (z : H v w ⊗[R] A) :
    ringEquiv R A ι w v (Ideal.Quotient.mk (ideal R A ι v w) z)=
      Ideal.Quotient.mk (ideal R A ι w v) (sourceEquiv R A ι w v z) :=
  rfl

/-- The actual original-source quotient families have regular overlap
isomorphisms, not only equality of classified points or module ranks. -/
@[expose] def transition : scheme R A ι w v ≅ scheme R A ι v w :=
  Scheme.Spec.mapIso (ringEquiv R A ι w v).toRingEquiv.toCommRingCatIso.op
@[reassoc] lemma transition_projection : (transition R A ι w v).hom ≫ projection R A ι v w=
    projection R A ι w v ≫ VaryingNormalizedOverlapScheme318.transition R A ι w v := by
  change Spec.map (CommRingCat.ofHom (ringEquiv R A ι w v).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (H v w) (ring R A ι v w)))=
      Spec.map (CommRingCat.ofHom (algebraMap (H w v) (ring R A ι w v))) ≫
        Spec.map (CommRingCat.ofHom f.toRingHom)
  rw [← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  change ringEquiv R A ι w v
    (Ideal.Quotient.mk (ideal R A ι v w) (a ⊗ₜ[R] (1 : A)))=
      Ideal.Quotient.mk (ideal R A ι w v) (f a ⊗ₜ[R] (1 : A))
  rw [ringEquiv_mk]
  rfl
end VaryingWordFamilyTransition318
