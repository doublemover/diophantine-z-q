module
public import NormalizedWholeScaleSquares318
public import NormalizedWholeProjectiveProper318
public section
noncomputable section
namespace NormalizedWholeScaleScheme318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open NormalizedWholeOverlap318 NormalizedWholeOpenMaps318 NormalizedWholeGluing318
open NormalizedWholeScaleEquiv318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c d a : Fin 4 → R)
  (s : Fin 4 → Rˣ) (h : ∀ i,c i=d i*(s i:R)^2)
@[expose] def finiteIso : finiteScheme R d a ≅ finiteScheme R c a :=
  Scheme.Spec.mapIso (finiteEquiv R c d a s h).toRingEquiv.toCommRingCatIso.op
@[expose] def infinityIso : infinityScheme R d a ≅ infinityScheme R c a :=
  Scheme.Spec.mapIso (infinityEquiv R c d a s h).toRingEquiv.toCommRingCatIso.op
@[expose] def commonIso : overlap R d a ≅ overlap R c a :=
  Scheme.Spec.mapIso (commonEquiv R c d a s h).toRingEquiv.toCommRingCatIso.op

theorem finite_square : (commonIso R c d a s h).hom ≫ intoFinite R c a=
    intoFinite R d a ≫ (finiteIso R c d a s h).hom := by
  change Spec.map (commonEquiv R c d a s h).toRingEquiv.toCommRingCatIso.hom ≫
    Spec.map (CommRingCat.ofHom (finiteMap R c a))=
    Spec.map (CommRingCat.ofHom (finiteMap R d a)) ≫
      Spec.map (finiteEquiv R c d a s h).toRingEquiv.toCommRingCatIso.hom
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f : CommRingCat.of (FiniteOrder R c a) ⟶ CommRingCat.of (CommonOrder R d a) =>
    Spec.map f) (CommRingCat.hom_ext (NormalizedWholeScaleSquares318.finite_square R c d a s h))

theorem infinity_square : (commonIso R c d a s h).hom ≫ intoInfinity R c a=
    intoInfinity R d a ≫ (infinityIso R c d a s h).hom := by
  change Spec.map (commonEquiv R c d a s h).toRingEquiv.toCommRingCatIso.hom ≫
    Spec.map (CommRingCat.ofHom (infinityMap R c a))=
    Spec.map (CommRingCat.ofHom (infinityMap R d a)) ≫
      Spec.map (infinityEquiv R c d a s h).toRingEquiv.toCommRingCatIso.hom
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f : CommRingCat.of (InfinityOrder R c a) ⟶ CommRingCat.of (CommonOrder R d a) =>
    Spec.map f) (CommRingCat.hom_ext (NormalizedWholeScaleSquares318.infinity_square R c d a s h))

theorem finite_inverse_square : (commonIso R c d a s h).inv ≫ intoFinite R d a=
    intoFinite R c a ≫ (finiteIso R c d a s h).inv := by
  apply (cancel_epi (commonIso R c d a s h).hom).mp
  rw [←Category.assoc,←Category.assoc,finite_square]
  simp only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id,Category.id_comp,Category.comp_id]

theorem infinity_inverse_square : (commonIso R c d a s h).inv ≫ intoInfinity R d a=
    intoInfinity R c a ≫ (infinityIso R c d a s h).inv := by
  apply (cancel_epi (commonIso R c d a s h).hom).mp
  rw [←Category.assoc,←Category.assoc,infinity_square]
  simp only [Category.assoc,Iso.hom_inv_id_assoc,Iso.hom_inv_id,Category.id_comp,Category.comp_id]

@[expose] def forward : scheme R d a ⟶ scheme R c a :=
  pushout.desc ((finiteIso R c d a s h).hom ≫ finiteChart R c a)
    ((infinityIso R c d a s h).hom ≫ infinityChart R c a) (by
      rw [←Category.assoc,←finite_square,Category.assoc]
      rw [show intoFinite R c a ≫ finiteChart R c a=intoInfinity R c a ≫ infinityChart R c a from pushout.condition]
      rw [←Category.assoc,infinity_square,Category.assoc])
@[expose] def backward : scheme R c a ⟶ scheme R d a :=
  pushout.desc ((finiteIso R c d a s h).inv ≫ finiteChart R d a)
    ((infinityIso R c d a s h).inv ≫ infinityChart R d a) (by
      rw [←Category.assoc,←finite_inverse_square,Category.assoc]
      rw [show intoFinite R d a ≫ finiteChart R d a=intoInfinity R d a ≫ infinityChart R d a from pushout.condition]
      rw [←Category.assoc,infinity_inverse_square,Category.assoc])

@[simp] theorem finite_forward : finiteChart R d a ≫ forward R c d a s h=
    (finiteIso R c d a s h).hom ≫ finiteChart R c a := pushout.inl_desc ..
@[simp] theorem infinity_forward : infinityChart R d a ≫ forward R c d a s h=
    (infinityIso R c d a s h).hom ≫ infinityChart R c a := pushout.inr_desc ..
@[simp] theorem finite_backward : finiteChart R c a ≫ backward R c d a s h=
    (finiteIso R c d a s h).inv ≫ finiteChart R d a := pushout.inl_desc ..
@[simp] theorem infinity_backward : infinityChart R c a ≫ backward R c d a s h=
    (infinityIso R c d a s h).inv ≫ infinityChart R d a := pushout.inr_desc ..

theorem forward_backward : forward R c d a s h ≫ backward R c d a s h=𝟙 _ := by
  apply pushout.hom_ext
  · change finiteChart R d a ≫ (forward R c d a s h ≫ backward R c d a s h)=finiteChart R d a ≫ 𝟙 _
    rw [←Category.assoc,finite_forward,Category.assoc,finite_backward]
    simp only [Iso.hom_inv_id_assoc,Category.comp_id]
  · change infinityChart R d a ≫ (forward R c d a s h ≫ backward R c d a s h)=infinityChart R d a ≫ 𝟙 _
    rw [←Category.assoc,infinity_forward,Category.assoc,infinity_backward]
    simp only [Iso.hom_inv_id_assoc,Category.comp_id]

theorem backward_forward : backward R c d a s h ≫ forward R c d a s h=𝟙 _ := by
  apply pushout.hom_ext
  · change finiteChart R c a ≫ (backward R c d a s h ≫ forward R c d a s h)=finiteChart R c a ≫ 𝟙 _
    rw [←Category.assoc,finite_backward,Category.assoc,finite_forward]
    simp only [Iso.inv_hom_id_assoc,Category.comp_id]
  · change infinityChart R c a ≫ (backward R c d a s h ≫ forward R c d a s h)=infinityChart R c a ≫ 𝟙 _
    rw [←Category.assoc,infinity_backward,Category.assoc,infinity_forward]
    simp only [Iso.inv_hom_id_assoc,Category.comp_id]

/-- Global square-scaling equivalence of the WHOLE two-chart models.
Both chart maps and all signed roots are specified. This is an isomorphism
of the possibly singular models, not their smooth normalization. -/
@[expose] def modelIso : scheme R d a ≅ scheme R c a where
  hom := forward R c d a s h
  inv := backward R c d a s h
  hom_inv_id := forward_backward R c d a s h
  inv_hom_id := backward_forward R c d a s h
end NormalizedWholeScaleScheme318
