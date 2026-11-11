module
public import NormalizedGenericPointExtension318
public section
noncomputable section
namespace NormalizedValuativeChartStructure318
open Polynomial CategoryTheory AlgebraicGeometry NormalizedWholeOverlap318 NormalizedWholeGluing318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (d a : Fin 4 → R)

theorem scalar_identity {A : Type u} [CommRing A] [Algebra R A] [Algebra R[X] A]
    [IsScalarTower R R[X] A] (T : R) (f : A →+* R)
    (hf : ∀ p : R[X],f (algebraMap R[X] A p)=Polynomial.eval T p) :
    f.comp (algebraMap R A)=RingHom.id R := by
  apply RingHom.ext
  intro r
  change f (algebraMap R A r)=r
  rw [IsScalarTower.algebraMap_apply R R[X] A]
  exact (hf (C r)).trans (Polynomial.eval_C _ _)

theorem finite_section (T : R) (f : FiniteOrder R d a →+* R)
    (hf : ∀ p : R[X],f (algebraMap R[X] (FiniteOrder R d a) p)=Polynomial.eval T p) :
    (Spec.map (CommRingCat.ofHom f) ≫ finiteChart R d a) ≫
      NormalizedWholeProjection318.structureMap R d a=𝟙 _ := by
  rw [Category.assoc,NormalizedWholeProjection318.finite_structure,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (f.comp (algebraMap R (FiniteOrder R d a))))=𝟙 _
  rw [scalar_identity R T f hf]
  exact Spec.map_id (CommRingCat.of R)

theorem infinity_section (w : R) (f : InfinityOrder R d a →+* R)
    (hf : ∀ p : R[X],f (algebraMap R[X] (InfinityOrder R d a) p)=Polynomial.eval w p) :
    (Spec.map (CommRingCat.ofHom f) ≫ infinityChart R d a) ≫
      NormalizedWholeProjection318.structureMap R d a=𝟙 _ := by
  rw [Category.assoc,NormalizedWholeProjection318.reciprocal_structure,←Spec.map_comp]
  change Spec.map (CommRingCat.ofHom (f.comp (algebraMap R (InfinityOrder R d a))))=𝟙 _
  rw [scalar_identity R w f hf]
  exact Spec.map_id (CommRingCat.of R)
end NormalizedValuativeChartStructure318
