module
public import ThreeJEllipticOrders318
public section
noncomputable section
open Filter Topology
namespace ThreeJActualFiniteOrders318
open ProjectiveLineFieldPoints318 ProjectiveLineComplexTopology318
open ThreeJManifoldHolomorphy318 ThreeProjectiveJPoints318 ThreeJAnalyticGerms318
open ThreeCompactParameter318 ThreeJEllipticOrders318
set_option maxHeartbeats 600000

local instance : TopologicalSpace ComplexPoints := complexPointTopology

/-- The actual finite target chart of the exact scheme map, evaluated in the
original finite source chart. Values outside that target chart are not used. -/
@[expose] def actualFiniteExpression (t : ℂ) : ℂ :=
  evaluationChart 1 (mapPoints (chartPoint (R:=ℚ) 1 t))

lemma actualFiniteExpression_eq {t : ℂ} (ht : t ≠ 0) :
    actualFiniteExpression =ᶠ[𝓝 t] J := by
  filter_upwards [eventually_ne_nhds ht] with z hz
  have hd : Polynomial.aeval z ThreeProjectiveJCertificates318.finiteDenominator ≠ 0 := by
    rw [(finite_evaluations z).2]
    exact pow_ne_zero 3 hz
  have he : mapPoints (chartPoint (R:=ℚ) 1 z)=chartPoint (R:=ℚ) 1 (J z) := by
    rw [finite_formula z hd,←ActualThreeJChartConsumer318.finite_J]
  unfold actualFiniteExpression
  rw [he,←evaluationChart_symm]
  exact (evaluationChart 1).right_inv (by rw [evaluationChart_target]; trivial)

lemma actualFiniteExpression_analytic {t : ℂ} (ht : t ≠ 0) :
    AnalyticAt ℂ actualFiniteExpression t :=
  (J_analytic ht).congr (actualFiniteExpression_eq ht).symm

/-- Local order of the actual map at the unramified finite preimage of j=0. -/
theorem actual_order_neg27 : meromorphicOrderAt actualFiniteExpression (-27)=1 := by
  rw [meromorphicOrderAt_congr
    ((actualFiniteExpression_eq (by norm_num : (-27:ℂ) ≠ 0)).filter_mono nhdsWithin_le_nhds)]
  exact order_at_neg27

/-- Local order of the actual map at the triply ramified finite preimage of j=0. -/
theorem actual_order_neg243 : meromorphicOrderAt actualFiniteExpression (-243)=3 := by
  rw [meromorphicOrderAt_congr
    ((actualFiniteExpression_eq (by norm_num : (-243:ℂ) ≠ 0)).filter_mono nhdsWithin_le_nhds)]
  exact order_at_neg243

/-- At every root of the original elliptic quadratic the actual finite target
coordinate, centered at1728, has order two. -/
theorem actual_order_1728 {t : ℂ} (ht : D t=0) :
    meromorphicOrderAt (fun z => actualFiniteExpression z-1728) t=2 := by
  have he : (fun z => actualFiniteExpression z-1728) =ᶠ[𝓝 t] (fun z => J z-1728) := by
    filter_upwards [actualFiniteExpression_eq (root_ne_zero ht)] with z hz
    rw [hz]
  rw [meromorphicOrderAt_congr (he.filter_mono nhdsWithin_le_nhds)]
  exact order_over_1728 ht

/-- Exact finite-fiber description at the two elliptic values, as equality of
actual scheme-valued points rather than equality of an auxiliary parameter. -/
theorem finite_zero_fiber {t : ℂ} (ht : t ≠ 0) :
    mapPoints (chartPoint (R:=ℚ) 1 t)=chartPoint (R:=ℚ) 1 (0:ℂ) ↔
      t= -27 ∨ t= -243 := by
  have hd : Polynomial.aeval t ThreeProjectiveJCertificates318.finiteDenominator ≠ 0 := by
    rw [(finite_evaluations t).2]
    exact pow_ne_zero 3 ht
  rw [finite_formula t hd,←ActualThreeJChartConsumer318.finite_J]
  exact (chartPoint_injective (R:=ℚ) (K:=ℂ) 1).eq_iff.trans (zero_fiber ht)

theorem finite_1728_fiber {t : ℂ} (ht : t ≠ 0) :
    mapPoints (chartPoint (R:=ℚ) 1 t)=chartPoint (R:=ℚ) 1 (1728:ℂ) ↔ D t=0 := by
  have hd : Polynomial.aeval t ThreeProjectiveJCertificates318.finiteDenominator ≠ 0 := by
    rw [(finite_evaluations t).2]
    exact pow_ne_zero 3 ht
  rw [finite_formula t hd,←ActualThreeJChartConsumer318.finite_J]
  exact (chartPoint_injective (R:=ℚ) (K:=ℂ) 1).eq_iff.trans (elliptic_fiber ht)

end ThreeJActualFiniteOrders318
