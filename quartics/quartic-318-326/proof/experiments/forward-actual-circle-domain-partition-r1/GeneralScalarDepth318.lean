module
public import AllPrimeSourceProgression318
public section
noncomputable section
namespace GeneralScalarDepth318
open ConcreteG8Domain (K)
open CoherentMultipleCharts318 (chartU)
open GeneratorScalarProgression318 (normCoefficient)
open ValuativeOrbitBounds318
open scoped Topology QuadraticAlgebra
set_option maxHeartbeats 1000000

/-- The actual all-prime neighborhood access produces arbitrary rational
coefficient depth before every later signed multiplier of one modulus. -/
theorem coefficients (p r : ℕ) [Fact p.Prime] :
    ∃ L : ℕ, 0<L ∧ ∀ m : ℤ,
      Bound (ConcretePadic318.rationalPlace p) (r:ℤ) (chartU ((L:ℤ)*m)).re ∧
      Bound (ConcretePadic318.rationalPlace p) (r:ℤ) (chartU ((L:ℤ)*m)).im := by
  have hreg : LocalIndexRegularity318.Regular 0 (ActualOrbitLocalFilter318.error p) := by
    simpa only [zero_add,one_mul] using AllPrimeSourceProgression318.actual_chart p 0 1 0
  let radius : ℝ := (p:ℝ)^(-(r:ℤ))
  have hr : 0<radius := by
    exact zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  obtain ⟨L,hL,haccess⟩ := hreg (Metric.ball 0 radius)
    (by simpa only [ActualOrbitLocalFilter318.error_zero] using Metric.ball_mem_nhds (0:Fin 4→ℚ_[p]) hr)
  refine ⟨L,hL,?_⟩
  intro m
  have he : ‖ActualOrbitLocalFilter318.error p ((L:ℤ)*m)‖≤radius := by
    have hm := haccess m
    simpa only [zero_add,Metric.mem_ball,dist_zero_right] using le_of_lt hm
  have hb := (pi_norm_le_iff_of_nonneg hr.le).mp he
  constructor
  · rw [Bound,PadicDetectorCoefficients318.rational_embedding]
    apply (HTail318.norm_le_iff_valuation p _ (r:ℤ)).mp
    simpa only [ActualOrbitLocalFilter318.error,Matrix.cons_val_zero] using hb 0
  · rw [Bound,PadicDetectorCoefficients318.rational_embedding]
    apply (HTail318.norm_le_iff_valuation p _ (r:ℤ)).mp
    simpa only [ActualOrbitLocalFilter318.error,Matrix.cons_val_succ,Matrix.cons_val_zero] using hb 1

lemma rational_depth (p : ℕ) [Fact p.Prime] (r : ℤ) (x : ℚ) (hx : x≠0)
    (h : Bound (ConcretePadic318.rationalPlace p) r x) : r≤padicValRat p x := by
  rw [Bound,ConcretePadic318.rational_value p x hx] at h
  exact_mod_cast h

/-- Actual norm and twice half trace, the literal source37 and2*source33,
are deep on the same constructed progression. Nonzero index excludes zero
leaves; extra cancellation at split places is allowed rather than denied. -/
theorem scalar_leaves (p r : ℕ) [Fact p.Prime] :
    ∃ L : ℕ, 0<L ∧ ∀ m : ℤ, m≠0 →
      2*(r:ℤ)≤padicValRat p (normCoefficient (chartU ((L:ℤ)*m))) ∧
      2*(r:ℤ)≤padicValRat p (2*((chartU ((L:ℤ)*m))^2).re) := by
  obtain ⟨L,hL,hcoeff⟩ := coefficients p r
  refine ⟨L,hL,?_⟩
  intro m hm
  have hn : (L:ℤ)*m≠0 := mul_ne_zero (by exact_mod_cast Nat.ne_of_gt hL) hm
  obtain ⟨ha,hb⟩ := hcoeff m
  let v := ConcretePadic318.rationalPlace p
  have hterm := bmul_unit_left v (bnat v 2) (bsquare v hb)
  constructor
  · apply rational_depth p _ _ (SeventeenScalarDepth318.norm_ne _ hn)
    simpa only [normCoefficient] using bsub v (bsquare v ha) hterm
  · apply rational_depth p _ _ (mul_ne_zero (by norm_num) (SeventeenScalarDepth318.half_trace_ne _ hn))
    have hf : Bound v (2*(r:ℤ)) ((chartU ((L:ℤ)*m))^2).re := by
      rw [ScalarHalfTraceDepth318.half_trace]
      exact badd v (bsquare v ha) hterm
    exact bmul_unit_left v (bnat v 2) hf

/-- The fixed scalar root label keeps its exact6-power and actual anchor
3-power. An additional common multiplier can satisfy every later local
inverse-norm depth without altering the Lucas construction. -/
theorem scalar_label (p A B N r : ℕ) [Fact p.Prime] :
    ∃ L : ℕ, 0<L ∧ ∀ d : ℕ, d≠0 →
      2*(r:ℤ)≤padicValRat p (ActualScalarRoot318.inverseNorm
        (ScalarPreparedResidues318.scalarLabel A B
          (PreparedAnchorLabels318.multiplier N (L*d)))) := by
  obtain ⟨L,hL,hdepth⟩ := scalar_leaves p r
  refine ⟨L,hL,?_⟩
  intro d hd
  have hm : L*d≠0 := mul_ne_zero (Nat.ne_of_gt hL) hd
  have hn := (ScalarPreparedResidues318.label_domains A B _
    (PreparedAnchorLabels318.multiplier_ne N _ hm)).1
  rw [ScalarTranslatedIndex318.scalar_inverse_norm _ (by omega)]
  have hi : ScalarPreparedResidues318.scalarLabel A B
      (PreparedAnchorLabels318.multiplier N (L*d))-1=
      (L:ℤ)*((6:ℤ)^(A+B+15)*3^N*(d:ℤ)) := by
    unfold ScalarPreparedResidues318.scalarLabel PreparedAnchorLabels318.multiplier
    push_cast
    ring
  rw [hi]
  exact (hdepth _ (mul_ne_zero (by positivity) (by exact_mod_cast hd))).1

end GeneralScalarDepth318
