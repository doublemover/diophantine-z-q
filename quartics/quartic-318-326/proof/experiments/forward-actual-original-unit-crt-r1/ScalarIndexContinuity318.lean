module
public import SeventeenScalarCenter318
public section
noncomputable section
namespace ScalarIndexContinuity318
open ArithmeticIndexRegularity318 LocalIndexRegularity318
open ScalarForwardWitness318
open scoped Topology QuadraticAlgebra
set_option maxHeartbeats 1000000

/-- The actual packed scalar expression is regular on its original common
index domain. It requires neither label guards nor detector quotient domains,
so it can be prepared before the later guard-avoiding center adjustment. -/
lemma actual (p : ℕ) [Fact p.Prime]
    (hb : ∀ a b h₀ : ℤ, Regular h₀ (fun h => ActualOrbitLocalFilter318.error p (a+b*h)))
    (q : ℚ) (labels : Fin 4 → ℤ) (n h₀ : ℤ) (hh : h₀≠0) (hr : inputR q≠0) :
    QRegular p h₀ (fun h => W (DetectorGateWitness318.witness q labels h) n) := by
  have hu : KRegular p h₀ CoherentMultipleCharts318.chartU := by
    simpa only [zero_add,one_mul] using ArithmeticIndexRegularity318.chartU p hb 0 1 h₀
  have hf : QRegular p h₀ (fun h => ((CoherentMultipleCharts318.chartU h)^2).re) :=
    KRegular.re (KRegular.pow hu 2)
  have hH : QRegular p h₀ (fun h => GeneratorScalarProgression318.normCoefficient (CoherentMultipleCharts318.chartU h)) := by
    unfold GeneratorScalarProgression318.normCoefficient
    have ha := KRegular.re hu
    have hb' := KRegular.im hu
    index_regularity
  have hnH := SeventeenScalarDepth318.norm_ne h₀ hh
  have hN := QRegular.add (QRegular.add (QRegular.const p h₀ 1)
    (QRegular.pow (QRegular.div hH (QRegular.const p h₀ (inputR q)) hr) 2))
    (QRegular.div (QRegular.mul (QRegular.const p h₀ 2) hf) (QRegular.const p h₀ (inputR q)) hr)
  have hden := QRegular.mul hH (QRegular.const p h₀ ((inputR q)^15))
  have hQ := QRegular.div (QRegular.const p h₀ (ActualScalarRoot318.inverseNorm n)) hden
    (mul_ne_zero hnH (pow_ne_zero _ hr))
  have he := QRegular.add (QRegular.pow hN 2)
    (QRegular.mul (QRegular.const p h₀ (inputR q)) (QRegular.pow hQ 2))
  simpa only [W,N,Q,ScalarActualInputs318.detector33,ScalarActualInputs318.detector37,
    DetectorGateWitness318.witness_input] using he

/-- Regular rational expressions preserve a proved local unit on a genuine
positive modulus. Zero at a later index is ruled out, not assigned value0. -/
theorem unit_progression (p : ℕ) [Fact p.Prime] (f : ℤ → ℚ) (h₀ : ℕ)
    (hr : QRegular p (h₀:ℤ) f) (hn : f (h₀:ℤ)≠0) (hv : padicValRat p (f (h₀:ℤ))=0) :
    ∃ L : ℕ, 0<L ∧ ∀ h : ℕ, Nat.ModEq L h h₀ → f (h:ℤ)≠0 ∧ padicValRat p (f (h:ℤ))=0 := by
  let z : ℚ_[p] := (f (h₀:ℤ):ℚ_[p])
  have hz : Padic.addValuation z=0 := by
    rw [←PadicDetectorCoefficients318.rational_embedding,ConcretePadic318.rational_value p _ hn,hv]
    rfl
  have hp : (0:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).pos
  let U : Set ℚ_[p] := Metric.ball z ((p:ℝ)⁻¹)
  obtain ⟨L,hL,haccess⟩ := nat_progression hr U (Metric.ball_mem_nhds _ (inv_pos.mpr hp))
  refine ⟨L,hL,?_⟩
  intro h hh
  have hsmall := haccess h hh
  have hnorm : ‖(f (h:ℤ):ℚ_[p])-z‖≤(p:ℝ)^(-(1:ℤ)) := by
    have he : ‖(f (h:ℤ):ℚ_[p])-z‖<(p:ℝ)⁻¹ := by simpa only [U,Metric.mem_ball,dist_eq_norm] using hsmall
    simpa using le_of_lt he
  have hdeep := (HTail318.norm_le_iff_valuation p _ 1).mp hnorm
  have hval : Padic.addValuation (f (h:ℤ):ℚ_[p])=0 := by
    have he := Padic.addValuation.map_eq_of_lt_sub (x:=z) (y:=(f (h:ℤ):ℚ_[p]))
      (by rw [hz]; exact lt_of_lt_of_le (by norm_num : (0:WithTop ℤ)<1) hdeep)
    simpa only [hz] using he
  have hnon : f (h:ℤ)≠0 := by intro he; rw [he] at hval; norm_num at hval
  refine ⟨hnon,?_⟩
  rw [←PadicDetectorCoefficients318.rational_embedding,ConcretePadic318.rational_value p _ hnon] at hval
  exact_mod_cast hval

end ScalarIndexContinuity318
