module
public import OriginalNormalOrderSameCenter318
public import OriginalNormalCenterCoordinateLattice318
public import FinitePlaceMultiplicativeDual318
public section
noncomputable section
namespace OriginalNormalOrderCotangentCoordinate318
open AlgebraicGeometry CategoryTheory NumberField Polynomial
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalOrderChart318 OriginalNormalOrderIntegralPoint318 OriginalNormalOrderSameCenter318
open scoped TensorProduct
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
  (ht : w (t : K c t) ≤ 1)
local notation "R" => V c t w
local notation "C" => Order c t w D
local notation "B" => SourceOpenRing c t w D
local notation "S" => sectionChart c t w D M ht

include M in
/-- The literal inclusion of the normal order in the original source
is etale because its Spec map factors the SAME original open immersion
through the proved actual normal-order chart. -/
lemma inclusion_etale :
    (IntegralFourRootNormalizationConductor318.normalOrder R
      (contacts c t w) D.coefficients).val.toRingHom.Etale := by
  let i := Spec.map (CommRingCat.ofHom
    (IntegralFourRootNormalizationConductor318.normalOrder R
      (contacts c t w) D.coefficients).val.toRingHom)
  letI : IsOpenImmersion (i ≫ chart c t w D M) := by
    rw [OriginalNormalOrderChart318.source]
    exact M.source_open
  letI : IsOpenImmersion i := IsOpenImmersion.of_comp i (chart c t w D M)
  exact HasRingHomProperty.Spec_iff.mp (inferInstance : Etale i)

/-- Evaluate the literal source differential with the specified point
algebra installed explicitly, never inferred from an unmentioned M. -/
@[expose] def sourceDifferential (z : C) : OriginalNormalSourceCotangent318.Fiber c t w D M := by
  letI : Algebra B (K c t) := M.fieldPoint.toAlgebra
  exact FramedCotangentFiber318.differential R B (K c t) z.val

structure ComparisonData where
  comparison : GenericCotangent c t w D M ht ≃ₗ[K c t]
    OriginalNormalSourceCotangent318.Fiber c t w D M
  differential : ∀ z : C, comparison
      (AffineSectionCotangentImage318.toGeneric S (K c t)
        (AffineSectionCotangentImage318.differential S z))=
    sourceDifferential c t w D M z

/-- Actual generic transport uses the normal-order inclusion and SAME
point. Every point-dependent algebra and tower is installed explicitly in
this producer, not registered as an instance with uninferable M/ht. -/
@[expose] def comparisonData : ComparisonData c t w D M ht := by
  letI : Algebra R C := (scalar c t w D).toAlgebra
  letI : Algebra C R := (evaluation c t w D M ht).toAlgebra
  letI : Algebra C (K c t) :=
    ((algebraMap R (K c t)).comp (evaluation c t w D M ht)).toAlgebra
  letI : Algebra C B :=
    (IntegralFourRootNormalizationConductor318.normalOrder R
      (contacts c t w) D.coefficients).val.toRingHom.toAlgebra
  letI : Algebra B (K c t) := M.fieldPoint.toAlgebra
  letI : IsScalarTower R C B := IsScalarTower.of_algebraMap_eq (fun r => by
    change algebraMap R B r=algebraMap R[X] B (Polynomial.C r)
    exact (IsScalarTower.algebraMap_apply R R[X] B r).symm)
  letI : IsScalarTower C B (K c t) := IsScalarTower.of_algebraMap_eq (fun z =>
    RingHom.congr_fun (field_square c t w D M ht) z)
  letI : IsScalarTower C R (K c t) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Algebra.Etale C B := RingHom.etale_algebraMap.mp (inclusion_etale c t w D M)
  let E := TensorProduct.AlgebraTensorModule.cancelBaseChange C R (K c t) (K c t)
    (KaehlerDifferential R C) ≪≫ₗ EtaleEvaluatedCotangent318.transport R C B (K c t)
  refine ⟨E,?_⟩
  intro z
  simp only [E,LinearEquiv.trans_apply,AffineSectionCotangentImage318.toGeneric,
    TensorProduct.mk_apply,AffineSectionCotangentImage318.differential,
    TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,one_smul]
  exact EtaleEvaluatedCotangent318.transport_differential R C B (K c t) z

@[expose] def genericComparison := (comparisonData c t w D M ht).comparison
lemma differential (z : C) : genericComparison c t w D M ht
    (AffineSectionCotangentImage318.toGeneric S (K c t)
      (AffineSectionCotangentImage318.differential S z))=sourceDifferential c t w D M z :=
  (comparisonData c t w D M ht).differential z

@[expose] def coordinateMap : Cotangent c t w D M ht →ₗ[R] K c t :=
  (((genericComparison c t w D M ht ≪≫ₗ OriginalNormalSourceCotangent318.frame c t w D M)
    .toLinearMap).restrictScalars R).comp (AffineSectionCotangentImage318.toGeneric S (K c t))
@[expose] def image : Submodule R (K c t) := (coordinateMap c t w D M ht).range

/-- Polynomial t is an ACTUAL integral normal-order element. Its
universal differential has exact original source dt coefficient1. -/
theorem coordinate_dt : coordinateMap c t w D M ht
    (AffineSectionCotangentImage318.differential S (algebraMap R[X] C X))=1 := by
  letI : Algebra B (K c t) := M.fieldPoint.toAlgebra
  change OriginalNormalSourceCotangent318.frame c t w D M
    (genericComparison c t w D M ht
      (AffineSectionCotangentImage318.toGeneric S (K c t)
        (AffineSectionCotangentImage318.differential S (algebraMap R[X] C X))))=1
  rw [differential]
  have he : ((algebraMap R[X] C X : C) : B)=
      IntegralNormalSourceDifferentialFrame318.coordinate R (contacts c t w) D.coefficients := by
    exact (IsScalarTower.algebraMap_apply R[X]
      (IntegralDistinctContactOpen318.Base R (contacts c t w) D.coefficients) B X).symm
  change OriginalNormalSourceCotangent318.frame c t w D M
    (FramedCotangentFiber318.differential R B (K c t)
      ((algebraMap R[X] C X : C) : B))=1
  rw [he]
  exact OriginalNormalSourceCotangent318.frame_dt c t w D M

theorem one_mem : (1 : K c t) ∈ image c t w D M ht :=
  ⟨AffineSectionCotangentImage318.differential S (algebraMap R[X] C X),
    coordinate_dt c t w D M ht⟩

/-- Every coefficient in the FULL integral dual of this actual chart's
cotangent image is integral. No codifferent or Hodge identity is used. -/
theorem dual_bound (z : K c t)
    (hz : z ∈ FinitePlaceMultiplicativeDual318.dual w (image c t w D M ht)) : w z ≤ 1 := by
  have h := (FinitePlaceMultiplicativeDual318.mem_iff w (image c t w D M ht) z).mp hz
    1 (one_mem c t w D M ht)
  rw [one_mul] at h
  exact (FinitePlaceMultiplicativeDual318.mem_unit_iff w z).mp h
end OriginalNormalOrderCotangentCoordinate318
