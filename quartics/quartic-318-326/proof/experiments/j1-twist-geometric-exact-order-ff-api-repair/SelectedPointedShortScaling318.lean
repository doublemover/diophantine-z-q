module
public import SelectedInfinityScaling318
import all WeierstrassGluing318
public section
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits WeierstrassGluing318

namespace SelectedPointedShortScaling318
open SelectedInfinityScaling318
variable {R : Type u} [CommRing R]
variable (A B C D : R) (r : Rˣ)
variable (hA : A = (r:R)^4*C) (hB : B = (r:R)^6*D)
local notation "F" => SelectedShortAffineScaling318.hom A B C D r hA hB
local notation "I" => infinityHom A B C D r hA hB
local notation "J" => overlapHom A B C D r hA hB

@[expose] def finiteMap : ShortAffineScheme318.scheme C D ⟶ ShortAffineScheme318.scheme A B :=
  Spec.map (CommRingCat.ofHom F.toRingHom)

@[expose] def infinityMap : InfinitySmooth318.scheme C D ⟶ InfinitySmooth318.scheme A B :=
  Spec.map (CommRingCat.ofHom I.toRingHom)

@[expose] def overlapMap : overlap C D ⟶ overlap A B :=
  Spec.map (CommRingCat.ofHom J.toRingHom)

local notation "Φ" => finiteMap A B C D r hA hB
local notation "Ψ" => infinityMap A B C D r hA hB
local notation "Ω" => overlapMap A B C D r hA hB

theorem finite_overlap : Ω ≫ intoAffine A B = intoAffine C D ≫ Φ := by
  rw [intoAffine_eq,intoAffine_eq]
  unfold overlapMap finiteMap
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (affine_overlap A B C D r hA hB))

theorem inf_overlap : Ω ≫ intoInfinity A B = intoInfinity C D ≫ Ψ := by
  unfold overlapMap infinityMap intoInfinity
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (infinity_overlap A B C D r hA hB))

/-- The true completed cubic restriction: glue the exact affine and
infinity coordinate maps along the original inverted-z chart. -/
@[expose] def gluedMap : scheme C D ⟶ scheme A B :=
  pushout.desc (Φ ≫ finiteChart A B) (Ψ ≫ infinityChart A B) (by
    rw [←Category.assoc,←Category.assoc,←finite_overlap,←inf_overlap,
      Category.assoc,Category.assoc]
    exact congrArg (fun f => Ω ≫ f) pushout.condition)

local notation "γ" => gluedMap A B C D r hA hB

@[simp, reassoc] theorem finite_glued :
    finiteChart C D ≫ γ = Φ ≫ finiteChart A B := pushout.inl_desc ..

@[simp, reassoc] theorem infinity_glued :
    infinityChart C D ≫ γ = Ψ ≫ infinityChart A B := pushout.inr_desc ..

private theorem finite_base : Φ ≫ ShortAffineScheme318.structureMap A B =
    ShortAffineScheme318.structureMap C D := by
  unfold finiteMap ShortAffineScheme318.structureMap
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact F.commutes a

private theorem infinity_base : Ψ ≫ InfinitySmooth318.structureMap A B =
    InfinitySmooth318.structureMap C D := by
  unfold infinityMap InfinitySmooth318.structureMap
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact I.commutes a

@[reassoc] theorem glued_base : γ ≫ structureMap A B = structureMap C D := by
  apply pushout.hom_ext
  · change finiteChart C D ≫ (γ ≫ structureMap A B) = finiteChart C D ≫ structureMap C D
    rw [←Category.assoc,finite_glued,Category.assoc,finiteChart_structure,finite_base,
      finiteChart_structure]
  · change infinityChart C D ≫ (γ ≫ structureMap A B) = infinityChart C D ≫ structureMap C D
    rw [←Category.assoc,infinity_glued,Category.assoc,infinityChart_structure,infinity_base,
      infinityChart_structure]

theorem origin_map : InfinitySmooth318.infinity C D ≫ Ψ =
    InfinitySmooth318.infinity A B := by
  unfold InfinitySmooth318.infinity infinityMap
  rw [←Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (origin_compat A B C D r hA hB))

/-- Preservation of the distinguished section as actual Scheme maps
over the entire original test ring. -/
@[reassoc] theorem zero_preserved :
    WeierstrassGluing318.infinity C D ≫ γ = WeierstrassGluing318.infinity A B := by
  unfold WeierstrassGluing318.infinity
  rw [Category.assoc,infinity_glued,←Category.assoc,origin_map]

local notation "hC" => inverse_coeff r 4 A C hA
local notation "hD" => inverse_coeff r 6 B D hB

private theorem affine_inv :
    F.comp (SelectedShortAffineScaling318.hom C D A B r⁻¹ hC hD) =
      AlgHom.id R (ShortAffineJacobian318.Ring C D) := by
  let e := SelectedShortAffineScaling318.equiv A B C D r hA hB
  apply AlgHom.ext
  intro a
  exact e.apply_symm_apply a

theorem finite_inverse : Φ ≫ finiteMap C D A B r⁻¹ hC hD = 𝟙 _ := by
  unfold finiteMap
  rw [←Spec.map_comp,←Spec.map_id]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (affine_inv A B C D r hA hB))

theorem infinity_inverse : Ψ ≫ infinityMap C D A B r⁻¹ hC hD = 𝟙 _ := by
  unfold infinityMap
  rw [←Spec.map_comp,←Spec.map_id]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (congrArg AlgHom.toRingHom (infinity_comp_inverse A B C D r hA hB))

theorem glued_inverse : γ ≫ gluedMap C D A B r⁻¹ hC hD = 𝟙 _ := by
  apply pushout.hom_ext
  · change finiteChart C D ≫ (γ ≫ gluedMap C D A B r⁻¹ hC hD) = finiteChart C D ≫ 𝟙 _
    rw [←Category.assoc,finite_glued,Category.assoc,finite_glued,←Category.assoc,
      finite_inverse,Category.id_comp,Category.comp_id]
  · change infinityChart C D ≫ (γ ≫ gluedMap C D A B r⁻¹ hC hD) = infinityChart C D ≫ 𝟙 _
    rw [←Category.assoc,infinity_glued,Category.assoc,infinity_glued,←Category.assoc,
      infinity_inverse,Category.id_comp,Category.comp_id]

/-- A pointed isomorphism of the actual completed cubics, with exactly
the chosen scale and its inverse. No reducedness condition. -/
@[expose] def iso : scheme C D ≅ scheme A B where
  hom := γ
  inv := gluedMap C D A B r⁻¹ hC hD
  hom_inv_id := glued_inverse A B C D r hA hB
  inv_hom_id := by
    simpa only [inv_inv] using glued_inverse C D A B r⁻¹ hC hD

end SelectedPointedShortScaling318

#print axioms SelectedPointedShortScaling318.glued_base
#print axioms SelectedPointedShortScaling318.zero_preserved
#print axioms SelectedPointedShortScaling318.iso
