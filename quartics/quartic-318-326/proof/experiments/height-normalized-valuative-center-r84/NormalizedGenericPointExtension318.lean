module
public import NormalizedGenericOverlapPoint318
public import NormalizedWholeProjectiveProper318
public section
noncomputable section
namespace NormalizedGenericPointExtension318
open Polynomial CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NormalizedWholeOverlap318 NormalizedWholeGluing318 IntegralRootPointMaps318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R K : Type u) [CommRing R] [Field K] [Algebra R K]
  (d a : Fin 4 → R) (t : K) (z : Fin 4 → K)
  (hz : ∀ i,(z i)^2=algebraMap R K (d i)*(t-algebraMap R K (a i)))

/-- A specified field point on the ACTUAL R-model, with its entire scalar
map and four signed roots. This definition does not assume a generic-fiber
base-change isomorphism with a separately constructed K-model. -/
@[expose] def point : Spec (CommRingCat.of K) ⟶ scheme R d a :=
  Spec.map (CommRingCat.ofHom (NormalizedGenericChartMaps318.finiteMap R K d a t z hz)) ≫
    finiteChart R d a

theorem reciprocal_point (ht : t≠0) :
    Spec.map (CommRingCat.ofHom
      (NormalizedGenericChartMaps318.infinityMap R K d a t⁻¹ (fun i => z i/t)
        (NormalizedGenericChartMaps318.reciprocal_roots R K d a t ht z hz))) ≫
      infinityChart R d a=point R K d a t z hz := by
  rw [←NormalizedGenericOverlapPoint318.infinity_restriction R K d a t ht z hz]
  change Spec.map (CommRingCat.ofHom (NormalizedWholeOpenMaps318.infinityMap R d a) ≫
    CommRingCat.ofHom (NormalizedGenericOverlapPoint318.commonMap R K d a t ht z hz)) ≫
      infinityChart R d a=_
  rw [Spec.map_comp,Category.assoc]
  change Spec.map (CommRingCat.ofHom (NormalizedGenericOverlapPoint318.commonMap R K d a t ht z hz)) ≫
    (intoInfinity R d a ≫ infinityChart R d a)=_
  rw [←pushout.condition,←Category.assoc]
  change (Spec.map (CommRingCat.ofHom (NormalizedGenericOverlapPoint318.commonMap R K d a t ht z hz)) ≫
    Spec.map (CommRingCat.ofHom (NormalizedWholeOpenMaps318.finiteMap R d a))) ≫ _ = _
  rw [←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    ((NormalizedGenericOverlapPoint318.commonMap R K d a t ht z hz).comp
      (NormalizedWholeOpenMaps318.finiteMap R d a))) ≫ _ = _
  rw [NormalizedGenericOverlapPoint318.finite_restriction]
  all_goals rfl

/-- A chart center with the correct polynomial map and signed roots gives
an equality of the entire field point, not only its contact coordinate. -/
theorem finite_extension (T : R) (hT : algebraMap R K T=t)
    (f : FiniteOrder R d a →+* R)
    (hf : ∀ p : R[X],f (algebraMap R[X] (FiniteOrder R d a) p)=Polynomial.eval T p)
    (hzf : ∀ i,algebraMap R K (f (FourRootOrderSigns318.generator
      (DVRNormalizedFiniteOrder318.coefficient R d a) i))=z i) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      (Spec.map (CommRingCat.ofHom f) ≫ finiteChart R d a)=point R K d a t z hz := by
  have h : (algebraMap R K).comp f=NormalizedGenericChartMaps318.finiteMap R K d a t z hz := by
    apply four_ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply,hf,Polynomial.eval_C,
          NormalizedGenericChartMaps318.finite_polynomial,Polynomial.aeval_C]
      · simp only [RingHom.comp_apply,hf,Polynomial.eval_X,hT,
          NormalizedGenericChartMaps318.finite_polynomial,Polynomial.aeval_X]
    · intro i
      rw [RingHom.comp_apply,hzf,NormalizedGenericChartMaps318.finite_generator]
  rw [←Category.assoc,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((algebraMap R K).comp f)) ≫ _ = _
  rw [h]
  all_goals rfl

theorem infinity_extension (ht : t≠0) (w : R) (hw : algebraMap R K w=t⁻¹)
    (f : InfinityOrder R d a →+* R)
    (hf : ∀ p : R[X],f (algebraMap R[X] (InfinityOrder R d a) p)=Polynomial.eval w p)
    (hzf : ∀ i,algebraMap R K (f (FourRootOrderSigns318.generator
      (DVRNormalizedInfinityOrder318.coefficient R d a) i))=z i/t) :
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫
      (Spec.map (CommRingCat.ofHom f) ≫ infinityChart R d a)=point R K d a t z hz := by
  have h : (algebraMap R K).comp f=
      NormalizedGenericChartMaps318.infinityMap R K d a t⁻¹ (fun i => z i/t)
        (NormalizedGenericChartMaps318.reciprocal_roots R K d a t ht z hz) := by
    apply four_ringHom_ext
    · apply Polynomial.ringHom_ext
      · intro r
        simp only [RingHom.comp_apply,hf,Polynomial.eval_C,
          NormalizedGenericChartMaps318.infinity_polynomial,Polynomial.aeval_C]
      · simp only [RingHom.comp_apply,hf,Polynomial.eval_X,hw,
          NormalizedGenericChartMaps318.infinity_polynomial,Polynomial.aeval_X]
    · intro i
      rw [RingHom.comp_apply,hzf,NormalizedGenericChartMaps318.infinity_generator]
  rw [←Category.assoc,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom ((algebraMap R K).comp f)) ≫ _ = _
  rw [h]
  exact reciprocal_point R K d a t z hz ht
end NormalizedGenericPointExtension318
