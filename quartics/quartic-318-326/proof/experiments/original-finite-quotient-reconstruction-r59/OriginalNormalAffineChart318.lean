module
public import OriginalNormalSectionClosure318
public import OriginalNormalClosureChartAction318
public section
noncomputable section
namespace OriginalNormalAffineChart318
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace
open OriginalNormalClosureGalois318
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {Y : Scheme} [IsIntegral Y] [Algebra (RatFunc ℚ) Y.functionField]
  [FiniteDimensional (RatFunc ℚ) Y.functionField] [IsGalois (RatFunc ℚ) Y.functionField]
  (U : Y.Opens) (hU : IsAffineOpen U) [Nonempty U]
  [Algebra ℚ[X] Γ(Y,U)] [IsScalarTower ℚ[X] Γ(Y,U) Y.functionField]
  [IsIntegrallyClosed Γ(Y,U)] [Algebra.IsIntegral ℚ[X] Γ(Y,U)]

/-- Integral-closure coordinates from the ACTUAL entire affine section ring. -/
@[expose] def sections : Γ(Y,U) ≃ₐ[ℚ[X]] Order Y.functionField := by
  letI : IsFractionRing Γ(Y,U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  exact OriginalNormalSectionClosure318.equivalence ℚ[X] Γ(Y,U) Y.functionField

@[expose] def specIso : Spec (CommRingCat.of (Order Y.functionField)) ≅ Spec Γ(Y,U) :=
  Scheme.Spec.mapIso (sections U hU).toRingEquiv.toCommRingCatIso.op

/-- The actual normal-closure chart is constructed, not supplied. -/
@[expose] def chart : Spec (CommRingCat.of (Order Y.functionField)) ⟶ Y :=
  (specIso U hU).hom ≫ hU.fromSpec

instance chart_openImmersion : IsOpenImmersion (chart U hU) := by
  unfold chart
  infer_instance

/-- The original germ map, not an arbitrary fraction-field equivalence. -/
lemma germ_fromSpec : Spec.map (Y.germToFunctionField U) ≫ hU.fromSpec =
    OriginalGenericStalkNaturality318.generic Y := by
  have hx : genericPoint Y ∈ U :=
    ((genericPoint_spec Y).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›)
  exact hU.fromSpecStalk_eq_fromSpecStalk hx

@[reassoc] theorem fraction_chart :
    OriginalNormalClosureChartAction318.fraction Y.functionField ≫ chart U hU =
      OriginalGenericStalkNaturality318.generic Y := by
  letI : IsFractionRing Γ(Y,U) Y.functionField :=
    functionField_isFractionRing_of_isAffineOpen Y U hU
  have h : OriginalNormalClosureChartAction318.fraction Y.functionField ≫
      (specIso U hU).hom = Spec.map (Y.germToFunctionField U) := by
    change Spec.map (CommRingCat.ofHom (algebraMap (Order Y.functionField) Y.functionField)) ≫
      Spec.map (CommRingCat.ofHom (sections U hU).toRingHom) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro a
    exact OriginalNormalSectionClosure318.equivalence_embedding ℚ[X] Γ(Y,U) Y.functionField a
  unfold chart
  rw [← Category.assoc, h, germ_fromSpec]

variable (p : Y ⟶ ProjectiveJLine318.scheme ℚ)
  (hbase : hU.fromSpec ≫ p =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] Γ(Y,U))) ≫ JLineAtlas318.chart ℚ 1)

include hbase in
@[reassoc] theorem chart_base : chart U hU ≫ p =
    OriginalNormalClosureChartAction318.chartBase Y.functionField := by
  unfold chart
  rw [Category.assoc, hbase, ← Category.assoc]
  change (Spec.map (CommRingCat.ofHom (sections U hU).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] Γ(Y,U)))) ≫ _ = _
  rw [← Spec.map_comp]
  unfold OriginalNormalClosureChartAction318.chartBase
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (sections U hU).commutes
end OriginalNormalAffineChart318
