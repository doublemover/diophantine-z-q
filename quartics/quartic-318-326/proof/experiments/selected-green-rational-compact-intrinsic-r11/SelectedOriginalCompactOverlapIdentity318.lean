module
public import SelectedOriginalGenericCompactCharts318
public import NormalizationSourceCompatibility318
public section
noncomputable section

open CategoryTheory AlgebraicGeometry Polynomial
open SelectedOriginalGenericChartClosures318 SelectedOriginalGenericCompactNormal318
open SelectedOriginalGenericClosureOverlap318 SelectedOriginalGenericCompactCharts318

namespace SelectedOriginalCompactOverlapIdentity318

variable (K : Type) [Field K] [Algebra JField K]
  [aK : Algebra ℚ K] [hTower : IsScalarTower ℚ JField K]

@[expose] def orderVal (i : Fin 2) : Order K i →+* K := by
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  exact (integralClosure ℚ[X] K).val.toRingHom

universe u

private theorem factored_original_identity {A B : CommRingCat.{u}} {Y : Scheme.{u}}
    (φ : A ⟶ B) (j : Spec A ⟶ Y) [IsOpenImmersion j]
    (f : Spec B ⟶ Y) [QuasiCompact f] [QuasiSeparated f] (hf : f = Spec.map φ ≫ j) :
    letI : Algebra A B := φ.hom.toAlgebra
    Spec.map (CommRingCat.ofHom (integralClosure A B).val.toRingHom) ≫
      (Spec.map (CommRingCat.ofHom (InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf).toRingHom) ≫
        ((NormalizationBaseCompatibility318.target_affine j).preimage f.fromNormalization).fromSpec) =
      f.toNormalization := by
  letI : Algebra A B := φ.hom.toAlgebra
  let C := CommRingCat.of (integralClosure A B)
  let e : integralClosure A B ≃ₐ[A] C := AlgEquiv.refl
  have hh := NormalizationSourceCompatibility318.factored_chart_original (C := C) φ j f hf e
  let a := InfinityGlobalChart318.sectionsEquiv_of_factor φ j f hf
  have hr : (a.trans e.toRingEquiv).toRingHom = a.toRingHom := by
    apply RingHom.ext
    intro x
    rfl
  have hv : (integralClosure A B).val.toRingHom.comp e.symm.toRingHom =
      (integralClosure A B).val.toRingHom := by
    apply RingHom.ext
    intro x
    rfl
  change Spec.map (CommRingCat.ofHom ((integralClosure A B).val.toRingHom.comp e.symm.toRingHom)) ≫
      (Spec.map (CommRingCat.ofHom (a.trans e.toRingEquiv).toRingHom) ≫
        ((NormalizationBaseCompatibility318.target_affine j).preimage f.fromNormalization).fromSpec) =
      f.toNormalization at hh
  rw [hr,hv] at hh
  exact hh

/-- The actual generic point in either affine chart really evaluates
by inclusion of its concrete order in the SAME original field K. -/
theorem chart_original (i : Fin 2) :
    Spec.map (CommRingCat.ofHom (orderVal K i)) ≫ chartEmbedding K i =
      (genericMap K).toNormalization := by
  letI : Algebra ℚ[X] K := (polynomial K i).toAlgebra
  unfold orderVal chartEmbedding actualSections
  exact factored_original_identity (CommRingCat.ofHom (polynomial K i)) (JLineAtlas318.chart ℚ i)
    (genericMap K) (genericMap_factor K i)

@[expose] def overlapVal (i : Fin 2) : Localization.Away (parameter K i) →+* K := by
  letI : Algebra Laurent K := (evaluation K i).toAlgebra
  letI : Algebra (Order K i) (OverlapOrder K i) := (restrictOrder K i).toAlgebra
  exact (integralClosure Laurent K).val.toRingHom.comp (restrictIso K i).toRingEquiv.toRingHom

private theorem overlapVal_apply (i : Fin 2) (v : Localization.Away (parameter K i)) :
    letI : Algebra (Order K i) (OverlapOrder K i) := (restrictOrder K i).toAlgebra
    overlapVal K i v = ((restrictIso K i v : OverlapOrder K i) : K) := rfl

theorem overlapVal_injective (i : Fin 2) : Function.Injective (overlapVal K i) := by
  letI : Algebra (Order K i) (OverlapOrder K i) := (restrictOrder K i).toAlgebra
  intro x y h
  apply (restrictIso K i).injective
  apply Subtype.ext
  exact (overlapVal_apply K i x).symm.trans (h.trans (overlapVal_apply K i y))

theorem overlapVal_order (i : Fin 2) :
    (overlapVal K i).comp (algebraMap (Order K i) (Localization.Away (parameter K i))) =
      orderVal K i := by
  letI : Algebra (Order K i) (OverlapOrder K i) := (restrictOrder K i).toAlgebra
  apply RingHom.ext
  intro x
  change overlapVal K i (algebraMap (Order K i) (Localization.Away (parameter K i)) x) = orderVal K i x
  rw [overlapVal_apply,AlgEquiv.commutes]
  change ((restrictOrder K i x : OverlapOrder K i) : K) = (x : K)
  exact restrictOrder_val K i x

private theorem bundled_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (a : R →+* S) (b : S →+* T) (c : R →+* T) (h : b.comp a = c) :
    CommRingCat.ofHom a ≫ CommRingCat.ofHom b = CommRingCat.ofHom c :=
  (CommRingCat.ofHom_comp a b).symm.trans
    (congrArg (fun w : R →+* T => CommRingCat.ofHom w) h)

private theorem spec_algebraMap_comp_of_value
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T] [Algebra R S]
    (b : S →+* T) (c : R →+* T) (h : b.comp (algebraMap R S) = c) :
    Spec.map (CommRingCat.ofHom b) ≫ Spec.algebraMap R S = Spec.map (CommRingCat.ofHom c) := by
  change Spec.map (CommRingCat.ofHom b) ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)) = _
  exact (Spec.map_comp (CommRingCat.ofHom (algebraMap R S)) (CommRingCat.ofHom b)).symm.trans
    (congrArg Spec.map (bundled_comp (algebraMap R S) b c h))

private theorem overlapEmbedding_eq (i : Fin 2) :
    overlapEmbedding K i =
      Spec.algebraMap (Order K i) (Localization.Away (parameter K i)) ≫ chartEmbedding K i := by
  unfold overlapEmbedding

theorem overlap_generic (i : Fin 2) :
    Spec.map (CommRingCat.ofHom (overlapVal K i)) ≫ overlapEmbedding K i =
      (genericMap K).toNormalization := by
  let R := Order K i
  let S := Localization.Away (parameter K i)
  let b : S →+* K := overlapVal K i
  let c : R →+* K := orderVal K i
  have ha : b.comp (algebraMap R S) = c := overlapVal_order K i
  have hs : Spec.map (CommRingCat.ofHom b) ≫ Spec.algebraMap R S = Spec.map (CommRingCat.ofHom c) :=
    @spec_algebraMap_comp_of_value R S K inferInstance inferInstance inferInstance inferInstance b c ha
  rw [overlapEmbedding_eq K i,← Category.assoc]
  exact (congrArg (fun v : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R) =>
    v ≫ chartEmbedding K i) hs).trans (chart_original K i)

theorem inverseOverlap_val (v : OverlapOrder K 1) :
    (((invertOverlap K).symm v : OverlapOrder K 0) : K) = (v : K) := by
  have h := (invertOverlap_val K ((invertOverlap K).symm v)).symm
  rwa [RingEquiv.apply_symm_apply] at h

/-- The concrete localization comparison acts as the identity IN K.
This gives an equality of ring maps, not just of subring images. -/
theorem concrete_overlap_square :
    (overlapVal K 0).comp (overlapIso K).symm.toRingHom = overlapVal K 1 := by
  letI : Algebra (Order K 0) (OverlapOrder K 0) := (restrictOrder K 0).toAlgebra
  letI : Algebra (Order K 1) (OverlapOrder K 1) := (restrictOrder K 1).toAlgebra
  apply RingHom.ext
  intro v
  simp only [RingHom.comp_apply,overlapVal_apply]
  change ((restrictIso K 0 ((restrictIso K 0).symm
    ((invertOverlap K).symm (restrictIso K 1 v))) : OverlapOrder K 0) : K) =
    ((restrictIso K 1 v : OverlapOrder K 1) : K)
  rw [AlgEquiv.apply_symm_apply,inverseOverlap_val]

/-- The geometric overlap isomorphism is exactly Spec of the explicit
reciprocal localization isomorphism. Equality is checked on the one
original generic K, and then descended by its injective ring embedding. -/
theorem actual_overlap_is_concrete :
    (actualOverlapIso K).hom =
      Spec.map (CommRingCat.ofHom (overlapIso K).symm.toRingHom) := by
  have hG :
      Spec.map (CommRingCat.ofHom (overlapVal K 0)) ≫ (actualOverlapIso K).hom =
        Spec.map (CommRingCat.ofHom (overlapVal K 1)) := by
    apply (cancel_mono (overlapEmbedding K 1)).mp
    simp only [Category.assoc,actualOverlapIso_fac,overlap_generic]
  obtain ⟨u,hu⟩ := Spec.map_surjective (actualOverlapIso K).hom
  rw [← hu] at hG ⊢
  rw [← Spec.map_comp] at hG
  have hu' := Spec.map_injective hG
  suffices u = CommRingCat.ofHom (overlapIso K).symm.toRingHom by rw [this]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  apply overlapVal_injective K 0
  have h₁ := congrArg (fun f => f.hom z) hu'
  have h₂ := RingHom.congr_fun (concrete_overlap_square K) z
  exact h₁.trans h₂.symm

end SelectedOriginalCompactOverlapIdentity318

#print axioms SelectedOriginalCompactOverlapIdentity318.chart_original
#print axioms SelectedOriginalCompactOverlapIdentity318.actual_overlap_is_concrete
