module
public import NormalizedGenericChartMaps318
public section
noncomputable section
namespace NormalizedGenericOverlapPoint318
open Polynomial IntegralRootPointMaps318 NormalizedWholeOverlap318 NormalizedReciprocalLaurent318
open NormalizedWholeOpenMaps318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
  (d a : Fin 4 → R) (t : K) (ht : t≠0)

@[expose] def scalarMap : Laurent R →ₐ[R] K :=
  IsLocalization.Away.liftAlgHom (f:=Polynomial.aeval t) (X:R[X])
    (by simpa only [Polynomial.aeval_X] using isUnit_iff_ne_zero.mpr ht)

theorem scalar_polynomial (p : R[X]) :
    scalarMap R K t ht (algebraMap R[X] (Laurent R) p)=Polynomial.aeval t p :=
  IsLocalization.Away.lift_eq _
    (by simpa only [Polynomial.aeval_X] using isUnit_iff_ne_zero.mpr ht) p

theorem scalar_coordinate : scalarMap R K t ht (coordinate R:Laurent R)=t := by
  rw [coordinate_value,scalar_polynomial,Polynomial.aeval_X]

theorem scalar_inverse : scalarMap R K t ht (↑(coordinate R)⁻¹:Laurent R)=t⁻¹ := by
  have h := map_units_inv (scalarMap R K t ht).toRingHom (coordinate R)
  simpa only [scalar_coordinate] using h

theorem scalar_reciprocal (p : R[X]) :
    scalarMap R K t ht (reciprocalMap R p)=Polynomial.aeval t⁻¹ p := by
  have h : (scalarMap R K t ht).comp (reciprocalMap R)=Polynomial.aeval t⁻¹ := by
    apply Polynomial.algHom_ext
    change scalarMap R K t ht (Polynomial.aeval (↑(coordinate R)⁻¹:Laurent R) X)=_
    rw [Polynomial.aeval_X,scalar_inverse,Polynomial.aeval_X]
  exact AlgHom.congr_fun h p

variable (z : Fin 4 → K)
  (hz : ∀ i,(z i)^2=algebraMap R K (d i)*(t-algebraMap R K (a i)))
local instance pointAlgebra : Algebra (Laurent R) K := (scalarMap R K t ht).toRingHom.toAlgebra

include hz in
theorem common_relation (i : Fin 4) :
    (z i)^2=algebraMap (Laurent R) K (finiteParameter R d a i) := by
  change (z i)^2=scalarMap R K t ht (algebraMap R[X] (Laurent R) _)
  rw [scalar_polynomial]
  simpa only [DVRNormalizedFiniteOrder318.coefficient,map_mul,map_sub,
    Polynomial.aeval_C,Polynomial.aeval_X] using hz i

@[expose] def commonMap : CommonOrder R d a →+* K :=
  (fourMap (finiteParameter R d a) z (common_relation R K d a t ht z hz)).toRingHom

theorem common_scalar (r : Laurent R) :
    commonMap R K d a t ht z hz (algebraMap (Laurent R) (CommonOrder R d a) r)=
      scalarMap R K t ht r :=
  (fourMap _ _ (common_relation R K d a t ht z hz)).commutes r

theorem common_generator (i : Fin 4) :
    commonMap R K d a t ht z hz (FourRootOrderSigns318.generator (finiteParameter R d a) i)=z i :=
  fourMap_generator _ _ _ i

/-- Both restrictions compare entire ring maps on the literal full overlap,
including all four signed roots and every polynomial coefficient. -/
theorem finite_restriction :
    (commonMap R K d a t ht z hz).comp (NormalizedWholeOpenMaps318.finiteMap R d a)=
      NormalizedGenericChartMaps318.finiteMap R K d a t z hz := by
  apply four_ringHom_ext
  · apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply,NormalizedWholeScalarMaps318.finite_polynomial,
      common_scalar,scalar_polynomial,NormalizedGenericChartMaps318.finite_polynomial]
  · intro i
    rw [RingHom.comp_apply,NormalizedWholeRootMaps318.finite_generator,common_generator,
      NormalizedGenericChartMaps318.finite_generator]

theorem infinity_restriction :
    (commonMap R K d a t ht z hz).comp (NormalizedWholeOpenMaps318.infinityMap R d a)=
      NormalizedGenericChartMaps318.infinityMap R K d a t⁻¹ (fun i => z i/t)
        (NormalizedGenericChartMaps318.reciprocal_roots R K d a t ht z hz) := by
  apply four_ringHom_ext
  · apply RingHom.ext
    intro p
    simp only [RingHom.comp_apply,NormalizedWholeScalarMaps318.infinity_polynomial,
      common_scalar,scalar_reciprocal,NormalizedGenericChartMaps318.infinity_polynomial]
  · intro i
    rw [RingHom.comp_apply,NormalizedWholeRootMaps318.infinity_generator]
    change commonMap R K d a t ht z hz
      (algebraMap (Laurent R) (CommonOrder R d a) (↑(coordinate R)⁻¹:Laurent R)*
        FourRootOrderSigns318.generator (finiteParameter R d a) i)=_
    rw [map_mul,common_scalar,scalar_inverse,common_generator,
      NormalizedGenericChartMaps318.infinity_generator]
    exact (div_eq_inv_mul _ _).symm
end NormalizedGenericOverlapPoint318
