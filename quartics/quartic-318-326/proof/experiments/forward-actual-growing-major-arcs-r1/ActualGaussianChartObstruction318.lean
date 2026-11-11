module
public import OriginalSignedLabelRankin318
public section
noncomputable section
namespace ActualGaussianChartObstruction318
open TernaryQuadraticLineCover318 LiteralAdjacentNormSlice318 LiteralQuarticSlice318
set_option maxHeartbeats 5000000

/-- Actual two Gaussian adjacent norms, with K retained in BOTH charts.
This is deliberately distinct from the older abstract P'/D predicate. -/
@[expose] def Obstruction (side : Bool) (κ t : ℤ) (y : Vector ℤ) (p : ℕ) : Prop :=
  (p:ℤ)∣(if side then P' κ t y else P κ t y) ∧ (p:ℤ)∣K κ t y

theorem original_source_iff (p : ℕ) [Fact p.Prime] (hp2 : p≠2)
    (κ t : ℤ) (ht : ¬(p:ℤ)∣t) (side : Bool) (v : Slice κ t side) :
    ((p:ℤ)∣G v.1.1 ∧ (p:ℤ)∣H v.1.1) ↔ Obstruction side κ t (project v.1.1) p := by
  cases side
  · exact first_chart_iff p hp2 κ t ht v
  · exact second_chart_iff p hp2 κ t ht v

/-- The old D substitution really is valid in the FIRST chart only.
No second-chart invocation of K_difference is permitted. -/
theorem first_abstract_iff (κ t : ℤ) (y : Vector ℤ) (p : ℕ) :
    Obstruction false κ t y p ↔ OriginalNormPointSieveTail318.pointObstruction false κ t y p := by
  change ((p:ℤ)∣P κ t y ∧ (p:ℤ)∣K κ t y) ↔
    ((p:ℤ)∣P κ t y ∧ (p:ℤ)∣D t y)
  constructor
  · rintro ⟨hP,hK⟩
    refine ⟨hP,?_⟩
    have hdiff : (p:ℤ)∣K κ t y-D t y := by
      rw [K_difference]
      exact dvd_mul_of_dvd_left hP _
    simpa only [sub_sub_cancel] using dvd_sub hK hdiff
  · rintro ⟨hP,hD⟩
    refine ⟨hP,?_⟩
    have hdiff : (p:ℤ)∣K κ t y-D t y := by
      rw [K_difference]
      exact dvd_mul_of_dvd_left hP _
    simpa only [sub_add_cancel] using dvd_add hdiff hD

/-- Concrete original source counterexample to the unconstructed
second-chart D bridge; encoded so later source audits cannot lose it. -/
theorem second_unshifted_counterexample :
    QuadricCRTAssembly318.equation (1:ℤ) ((-5,-1),(-5,-1),0)=0 ∧
    x0 ((-5,-1),(-5,-1),0)=-10 ∧
    (17:ℤ)∣G ((-5,-1),(-5,-1),0) ∧
    (17:ℤ)∣H ((-5,-1),(-5,-1),0) ∧
    ¬(17:ℤ)∣D (-10) (0,-2,0) := by
  norm_num [QuadricCRTAssembly318.equation,x0,G,H,D]

end ActualGaussianChartObstruction318
