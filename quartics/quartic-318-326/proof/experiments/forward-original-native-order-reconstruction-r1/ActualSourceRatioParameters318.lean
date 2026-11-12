module
public import ActualPrimaryLogPrecision318
public section
noncomputable section
namespace ActualSourceRatioParameters318
open ConcreteG8Domain (K pair)
open CoherentMultipleCharts318 (chartU chartV)
open CompressedOrientation318 (k m D mid)
open CompressedAnchorWitness318 (shiftWitness)
open ActualPadeRatios318 PadeRatioWitness318 Pade21Domains
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

lemma base_mid (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    mid (base q labels h)=(chartU h)^2*shiftWitness (chartU h) (chartV h) := by
  ext <;> simp [mid,base,CoherentMultiplePrefix318.witness,RealGuardWitness318.fill,
    CompressedAnchorWitness318.fill,pair]

lemma base_A (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    A (base q labels h)=k*chartV h/chartU h := by
  unfold A
  rw [base_shift,base_mid]
  have he := CompressedAnchorWitness318.ordinate_identity (chartU h) (chartV h)
  linear_combination he

/-- The literal primary source ratio is exactly the original z(nH)/z(H),
including its sign and scalar k. No complete source solution is assumed. -/
lemma primary (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (hzero : h≠0) (j : Fin 4) :
    (construct (base q labels h)).primaryRatio j=
      (-chartU (labels j*h)/chartV (labels j*h))/(-chartU h/chartV h) := by
  have hu : chartU h≠0 := fun he => hzero ((CoherentMultipleCharts318.chartU_zero_iff h).mp he)
  dsimp only [construct]
  rw [base_A,base_u,base_v]
  simp only [CoherentMultiplePrefix318.u,CoherentMultiplePrefix318.v,
    CoherentMultiplePrefix318.parameters,Fin.append_left]
  field_simp [hu,CompressedPoint318.k_ne,CoherentAdditionV318.chartV_ne] <;> ring

/-- Oriented translated ordinate, not a choice of the sign of a square root. -/
lemma translated_v (h : ℤ) (hzero : h≠0) :
    chartV (h-1)=chartU h*CompressedChartDomains318.anchorB (chartU h) (chartV h)/k := by
  have hu : chartU h≠0 := fun he => hzero ((CoherentMultipleCharts318.chartU_zero_iff h).mp he)
  have hc := CoherentMultipleCharts318.chart_curve h
  have hk := CompressedPoint318.constant_equation
  rw [sub_eq_add_neg,CoherentAdditionV318.chartV_add,
    CoherentMultipleCharts318.chartU_negative,CoherentMultipleCharts318.chartV_negative,
    ScalarTranslatedIndex318.chartU_one_inverse,ScalarTranslatedIndex318.chartV_one]
  rw [CoherentMultipleCharts318.D_eq.symm]
  unfold ReciprocalGroup318.sumV CompressedChartDomains318.anchorB shiftWitness
  field_simp [hu,CompressedPoint318.k_ne,CompressedAnchorWitness318.denominator_nonzero,
    CoherentRootSign318.addition_denominator_ne]
  ring_nf
  rw [hc,hk]
  ring

lemma argument (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (hzero : h≠0) :
    arg (base q labels h)=D*(chartU (h-1))^4 := by
  rw [arg,base_fV,ScalarTranslatedIndex318.shifted_chart h hzero]
  ring

/-- The common denominator is the actual G-Padé logarithm at H−P. -/
lemma common_parameter (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (hzero : h≠0) :
    common (base q labels h)=(-chartU (h-1)/chartV (h-1))*
      (PG (D*(chartU (h-1))^4)/QG (D*(chartU (h-1))^4)) := by
  have hu : chartU h≠0 := fun he => hzero ((CoherentMultipleCharts318.chartU_zero_iff h).mp he)
  have hB := CompressedChartDomains318.anchorB_ne _ _ hu (CoherentMultipleCharts318.chart_curve h)
  rw [common,polynomial,base_shift,base_B,argument q labels h hzero,
    translated_v h hzero,ScalarTranslatedIndex318.shifted_chart h hzero]
  field_simp [hu,CompressedPoint318.k_ne,hB] <;> ring

/-- All four actual primary errors inherit the depth16 analytic estimate
from the original integer group law at a depth4 center. -/
theorem primary_precision (p : ℕ) [Fact p.Prime] (hp : 19≤p)
    (rho : ℚ_[p]) (hr : rho^2=2) (h7 : ¬p∣49)
    (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (hzero : h≠0)
    (hn : ∀ j, labels j≠0)
    (hbase : ValuativeOrbitBounds318.Near (ConcretePadic318.place p rho hr) 4 (chartU h) (chartV h))
    (hall : ∀ j, ValuativeOrbitBounds318.Near (ConcretePadic318.place p rho hr) 4
      (chartU (labels j*h)) (chartV (labels j*h))) :
    ∀ j, ValuativeOrbitBounds318.Bound (ConcretePadic318.place p rho hr) 16
      ((construct (base q labels h)).primaryRatio j-(labels j:K)) := by
  intro j
  rw [primary q labels h hzero j]
  exact ActualPrimaryLogPrecision318.original_ratio p hp rho hr h7 h (labels j) 4 hzero
    (hn j) (by norm_num) hbase (hall j)

end ActualSourceRatioParameters318
