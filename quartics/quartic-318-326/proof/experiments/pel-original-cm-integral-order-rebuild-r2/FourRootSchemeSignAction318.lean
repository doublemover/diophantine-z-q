module
public import FourRootGluedScheme318
public import FourRootLocalizedSignAction318
public import FourRootActionStabilizers318
public section
noncomputable section
namespace FourRootSchemeSignAction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FourRootGluedScheme318 FourRootCoordinateRingSigns318 FourRootLocalizedSignAction318
variable (b:Fin 4→ℂ) (g:FourBinaryCharacters318.Group)
@[expose] def finiteMap:finiteScheme b⟶finiteScheme b:=
  Spec.map (CommRingCat.ofHom (finiteEnd b g).toRingHom)
@[expose] def infinityMap:infinityScheme b⟶infinityScheme b:=
  Spec.map (CommRingCat.ofHom (infinityEnd b g).toRingHom)
@[expose] def overlapMap:overlapScheme b⟶overlapScheme b:=
  Spec.map (CommRingCat.ofHom (overlapEnd b g).toRingHom)
@[reassoc] lemma finite_square:
    intoFinite b≫finiteMap b g=overlapMap b g≫intoFinite b:=by
  rw [intoFinite_eq]
  unfold finiteMap overlapMap
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f:FourRootCoordinateOverlap318.Affine b→ₐ[ℂ]
    FourRootCoordinateOverlap318.InfinityOverlap b=>Spec.map (CommRingCat.ofHom f.toRingHom))
      (FourRootLocalizedSignAction318.finite_square b g).symm
@[reassoc] lemma infinity_square:
    intoInfinity b≫infinityMap b g=overlapMap b g≫intoInfinity b:=by
  unfold intoInfinity infinityMap overlapMap
  rw [←Spec.map_comp,←Spec.map_comp]
  exact congrArg (fun f:FourRootCoordinateOverlap318.Infinity b→ₐ[ℂ]
    FourRootCoordinateOverlap318.InfinityOverlap b=>Spec.map (CommRingCat.ofHom f.toRingHom))
      (FourRootLocalizedSignAction318.infinity_square b g).symm

/-- The whole Scheme action is glued from the ACTUAL coordinate-ring
sign maps through their literal localization covariance. -/
@[expose] def action:scheme b⟶scheme b:=
  pushout.desc (finiteMap b g≫finiteChart b) (infinityMap b g≫infinityChart b) (by
    rw [←Category.assoc,finite_square,Category.assoc,chart_overlap,
      ←Category.assoc,←infinity_square,Category.assoc])
@[reassoc,simp] lemma finite_action:finiteChart b≫action b g=finiteMap b g≫finiteChart b:=
  pushout.inl_desc ..
@[reassoc,simp] lemma infinity_action:infinityChart b≫action b g=infinityMap b g≫infinityChart b:=
  pushout.inr_desc ..
lemma finiteMap_square:finiteMap b g≫finiteMap b g=𝟙 _:=by
  unfold finiteMap
  rw [←Spec.map_comp]
  have he:(finiteEnd b g).comp (finiteEnd b g)=AlgHom.id ℂ (FourRootCoordinateOverlap318.Affine b):=by
    ext a;exact finite_involutive b g a
  have hh:=congrArg (fun f:FourRootCoordinateOverlap318.Affine b→ₐ[ℂ]
    FourRootCoordinateOverlap318.Affine b=>Spec.map (CommRingCat.ofHom f.toRingHom)) he
  simpa using hh
lemma infinityMap_square:infinityMap b g≫infinityMap b g=𝟙 _:=by
  unfold infinityMap
  rw [←Spec.map_comp]
  have he:(infinityEnd b g).comp (infinityEnd b g)=AlgHom.id ℂ (FourRootCoordinateOverlap318.Infinity b):=by
    ext a;exact infinity_involutive b g a
  have hh:=congrArg (fun f:FourRootCoordinateOverlap318.Infinity b→ₐ[ℂ]
    FourRootCoordinateOverlap318.Infinity b=>Spec.map (CommRingCat.ofHom f.toRingHom)) he
  simpa using hh
lemma action_square:action b g≫action b g=𝟙 _:=by
  apply FourRootGluedScheme318.hom_ext
  · simp only [finite_action_assoc,finite_action,Category.comp_id,←Category.assoc,
      finiteMap_square,Category.id_comp]
  · simp only [infinity_action_assoc,infinity_action,Category.comp_id,←Category.assoc,
      infinityMap_square,Category.id_comp]
@[expose] def schemeIso:scheme b≅scheme b where
  hom:=action b g
  inv:=action b g
  hom_inv_id:=action_square b g
  inv_hom_id:=action_square b g

/-- The original complex coefficient base is fixed as a Scheme map. -/
@[reassoc] theorem over_base:action b g≫structureMap b=structureMap b:=by
  apply FourRootGluedScheme318.hom_ext
  · rw [finite_action_assoc,finite_structure,finite_structure]
    unfold finiteMap finiteBase
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (finiteEnd b g).commutes a
  · rw [infinity_action_assoc,infinity_structure,infinity_structure]
    unfold infinityMap infinityBase
    rw [←Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact (infinityEnd b g).commutes a

lemma finiteMap_mul (h:FourBinaryCharacters318.Group):
    finiteMap b (g*h)=finiteMap b g≫finiteMap b h:=by
  unfold finiteMap
  rw [←Spec.map_comp]
  exact congrArg (fun f:FourRootCoordinateOverlap318.Affine b→ₐ[ℂ]
    FourRootCoordinateOverlap318.Affine b=>Spec.map (CommRingCat.ofHom f.toRingHom))
      (FourRootActionStabilizers318.finiteEnd_mul b g h)
lemma infinityMap_mul (h:FourBinaryCharacters318.Group):
    infinityMap b (g*h)=infinityMap b g≫infinityMap b h:=by
  unfold infinityMap
  rw [←Spec.map_comp]
  exact congrArg (fun f:FourRootCoordinateOverlap318.Infinity b→ₐ[ℂ]
    FourRootCoordinateOverlap318.Infinity b=>Spec.map (CommRingCat.ofHom f.toRingHom))
      (FourRootActionStabilizers318.infinityEnd_mul b g h)
/-- Exact full group law as Scheme morphisms, not merely pointwise. -/
theorem action_mul (h:FourBinaryCharacters318.Group):
    action b (g*h)=action b g≫action b h:=by
  apply FourRootGluedScheme318.hom_ext
  · simp only [finite_action,finite_action_assoc,finiteMap_mul,Category.assoc]
  · simp only [infinity_action,infinity_action_assoc,infinityMap_mul,Category.assoc]
theorem action_one:action b 1=𝟙 _:=by
  have he:=action_mul b 1 1
  simpa only [mul_one,action_square] using he
end FourRootSchemeSignAction318
