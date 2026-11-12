module
public import OriginalPointFinitePlaceCenter318
public import IntegralEvaluatedPointCharts318
public section
noncomputable section
namespace OriginalPointPrimitiveChart318
open AlgebraicGeometry CategoryTheory NumberField
open OriginalPointFinitePlaceRoots318 ContactArithmeticDenominator318
open IntegralEvaluatedPointCharts318 ActualFinitePlaceIntegers318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (t : ℚ) (v : FinitePlace (K c t))
  (hv : v (denominator c:K c t)=1)

/-- The original point has an actual integral chart evaluation whose original
J² coefficient pair is primitive and has exactly its original t ratio.
Neither a chart center nor a coefficient integrality bound is a premise. -/
theorem exists_primitive_chart :
    ∃ (o : Option (Fin 4)) (φ : ChartRing (V c t v) (localTwists c t v hv) o →+* V c t v),
      Spec.map (CommRingCat.ofHom (algebraMap (V c t v) (K c t))) ≫
        Spec.map (CommRingCat.ofHom φ) ≫ embedding (V c t v) (localTwists c t v hv) o=
          IntegralValuativeGenericPoint318.point (V c t v) (K c t) (localTwists c t v hv)
            (t:K c t) (roots c t) (local_root_equations c t v hv) ∧
      algebraMap (V c t v) (K c t) (φ (coefficient (V c t v) (localTwists c t v hv) o 1))=
        (t:K c t)*algebraMap (V c t v) (K c t)
          (φ (coefficient (V c t v) (localTwists c t v hv) o 0)) ∧
      max (v (algebraMap (V c t v) (K c t) (φ (coefficient (V c t v) (localTwists c t v hv) o 0))))
        (v (algebraMap (V c t v) (K c t) (φ (coefficient (V c t v) (localTwists c t v hv) o 1))))=1 := by
  obtain ⟨o,φ,hg,hr⟩ := IntegralEvaluatedPointCharts318.exists_chart
    (V c t v) (localTwists c t v hv) (K c t) (t:K c t) (roots c t)
    (local_root_equations c t v hv) (ContactFinitePlaceBaseMap318.separation_unit c v hv)
  refine ⟨o,φ,hg,hr,?_⟩
  exact IntegralUnitPairNorm318.pair_max ((algebraMap (V c t v) (K c t)).comp φ) v
    (center_bound v φ) _ _ (primitive _ _ (ContactFinitePlaceBaseMap318.separation_unit c v hv) o)
end OriginalPointPrimitiveChart318
