module
public import IntegralWholeProjectiveProjection318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public section
noncomputable section
namespace IntegralWholeChartFiniteness318
open Polynomial AlgebraicGeometry CategoryTheory
open IntegralWholeReciprocalOrders318 IntegralWholeOrderScalarMaps318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R : Type*} [CommRing R]

/-- A unit change of the actual polynomial coordinate, with explicit inverse. -/
@[expose] def scaleCoordinate (a : Rˣ) : R[X] ≃ₐ[R] R[X] :=
  AlgEquiv.ofAlgHom (Polynomial.aeval (C (a:R)*X))
    (Polynomial.aeval (C (↑a⁻¹:R)*X))
    (by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply,Polynomial.aeval_X,map_mul,Polynomial.aeval_C,
        AlgHom.id_apply,Polynomial.algebraMap_eq]
      rw [←mul_assoc,←map_mul,Units.inv_mul,map_one,one_mul])
    (by
      apply Polynomial.algHom_ext
      simp only [AlgHom.comp_apply,Polynomial.aeval_X,map_mul,Polynomial.aeval_C,
        AlgHom.id_apply,Polynomial.algebraMap_eq]
      rw [←mul_assoc,←map_mul,Units.mul_inv,map_one,one_mul])

@[simp] theorem scaleCoordinate_X (a : Rˣ) : scaleCoordinate a X=C (a:R)*X :=
  Polynomial.aeval_X _

variable (R) (c : Fin 4 → Rˣ)
theorem reciprocal_factor :
    (infinityProjection R c).toRingHom=
      (algebraMap R[X] (InfinityOrder R c)).comp (scaleCoordinate (c 0)⁻¹).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    change infinityProjection R c (C r)=
      algebraMap R[X] (InfinityOrder R c) (scaleCoordinate (c 0)⁻¹ (C r))
    have hc : scaleCoordinate (c 0)⁻¹ (C r) = C r := by
      simpa only [Polynomial.algebraMap_eq] using (scaleCoordinate (c 0)⁻¹).commutes r
    rw [hc,infinityProjection,Polynomial.aeval_C]
    rfl
  · change infinityProjection R c X=
      algebraMap R[X] (InfinityOrder R c) (scaleCoordinate (c 0)⁻¹ X)
    rw [scaleCoordinate_X,map_mul]
    exact Polynomial.aeval_X _

instance finite_chart_finite : IsFinite (Spec.map (CommRingCat.ofHom
    (algebraMap R[X] (FiniteOrder R c)))) :=
  (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- The literal reciprocal projective-coordinate map is finite; its scalar
map is the unit coordinate automorphism followed by the rank8 order map. -/
instance reciprocal_chart_finite : IsFinite (Spec.map
    (CommRingCat.ofHom (infinityProjection R c).toRingHom)) := by
  letI : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R[X] (InfinityOrder R c)))) :=
    (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)
  rw [reciprocal_factor,CommRingCat.ofHom_comp,Spec.map_comp]
  change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R[X] (InfinityOrder R c))) ≫
    Spec.map (scaleCoordinate (c 0)⁻¹).toRingEquiv.toCommRingCatIso.hom)
  infer_instance
end IntegralWholeChartFiniteness318
