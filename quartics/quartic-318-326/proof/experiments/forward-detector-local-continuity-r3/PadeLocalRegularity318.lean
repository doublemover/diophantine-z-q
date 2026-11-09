module
public import PrefixLocalRegularity318
public section
noncomputable section
namespace PadeLocalRegularity318
open ArithmeticIndexRegularity318
open ConcreteG8Domain (K pair)
open PadeRatioWitness318 ActualPadeRatios318 Pade21Domains
open CompressedOrientation318 (k m D shift mid fV)
set_option maxHeartbeats 1000000

variable (p : ℕ) [Fact p.Prime] (h₀ : ℤ) (w : ℤ → CircuitReplay.Assignment)
  (hw : ∀ i, QRegular p h₀ (fun h => w h i))

include hw in
lemma U (j : Fin 8) : KRegular p h₀ (fun h => u (w h) j) := by
  unfold u
  index_regularity
include hw in
lemma V (j : Fin 8) : KRegular p h₀ (fun h => v (w h) j) := by
  unfold v
  index_regularity
include hw in
lemma Shift : KRegular p h₀ (fun h => shift (w h)) := by unfold shift; index_regularity
include hw in
lemma Mid : KRegular p h₀ (fun h => mid (w h)) := by unfold mid; index_regularity
include hw in
lemma FV : KRegular p h₀ (fun h => fV (w h)) := by unfold fV; index_regularity
include hw in
lemma AA : KRegular p h₀ (fun h => A (w h)) := by
  have hs := Shift p h₀ w hw
  have hm := Mid p h₀ w hw
  unfold A
  index_regularity
include hw in
lemma BB : KRegular p h₀ (fun h => B (w h)) := by
  have hs := Shift p h₀ w hw
  have hf := FV p h₀ w hw
  unfold B
  index_regularity
include hw in
lemma Arg : KRegular p h₀ (fun h => arg (w h)) := by
  have hf := FV p h₀ w hw
  unfold arg
  index_regularity
include hw in
lemma pg : KRegular p h₀ (fun h => PG (arg (w h))) := by
  have ha := Arg p h₀ w hw
  unfold PG
  index_regularity
include hw in
lemma qg : KRegular p h₀ (fun h => QG (arg (w h))) := by
  have ha := Arg p h₀ w hw
  unfold QG
  index_regularity
include hw in
lemma polynomial (hG : QG (arg (w h₀))≠0) :
    KRegular p h₀ (fun h => ActualPadeRatios318.polynomial (w h)) :=
  KRegular.div (pg p h₀ w hw) (qg p h₀ w hw) hG
include hw in
lemma common (hG : QG (arg (w h₀))≠0) (hB : B (w h₀)≠0) :
    KRegular p h₀ (fun h => ActualPadeRatios318.common (w h)) := by
  have hs := Shift p h₀ w hw
  have hp := polynomial p h₀ w hw hG
  unfold ActualPadeRatios318.common
  apply KRegular.div
  · index_regularity
  · exact BB p h₀ w hw
  · exact hB
include hw in
lemma alternate (j : Fin 4) (hJ : QJ (v (w h₀) (j.natAdd 4)-1)≠0) :
    KRegular p h₀ (fun h => alternatePolynomial (w h) j) := by
  have hv := V p h₀ w hw (j.natAdd 4)
  by_cases hj : j=0
  · subst j
    simp only [alternatePolynomial,if_pos rfl]
    apply KRegular.sub (KRegular.const p h₀ 1)
    apply KRegular.div
    · index_regularity
    · exact KRegular.const p h₀ 5
    · norm_num
  · simp only [alternatePolynomial,if_neg hj]
    apply KRegular.div
    · unfold PJ
      index_regularity
    · unfold QJ
      index_regularity
    · exact hJ
include hw in
lemma primary (j : Fin 4) (hv : v (w h₀) (j.castAdd 4)≠0) :
    KRegular p h₀ (fun h => (construct (w h)).primaryRatio j) := by
  have hu := U p h₀ w hw (j.castAdd 4)
  have hv' := V p h₀ w hw (j.castAdd 4)
  have ha := AA p h₀ w hw
  dsimp only [construct]
  apply KRegular.div
  · index_regularity
  · index_regularity
  · exact mul_ne_zero CompressedPoint318.k_ne hv
include hw in
lemma alternateRatio (j : Fin 4) (hG : QG (arg (w h₀))≠0) (hB : B (w h₀)≠0)
    (hC : ActualPadeRatios318.common (w h₀)≠0) (hJ : QJ (v (w h₀) (j.natAdd 4)-1)≠0) :
    KRegular p h₀ (fun h => (construct (w h)).alternateRatio j) := by
  have hu := U p h₀ w hw (j.natAdd 4)
  have hj := alternate p h₀ w hw j hJ
  dsimp only [construct]
  apply KRegular.div
  · index_regularity
  · exact common p h₀ w hw hG hB
  · exact hC

include hw in
lemma fill (hG : QG (arg (w h₀))≠0) (hB : B (w h₀)≠0)
    (hC : ActualPadeRatios318.common (w h₀)≠0)
    (hJ : ∀ j : Fin 4, QJ (v (w h₀) (j.natAdd 4)-1)≠0)
    (hv : ∀ j : Fin 4, v (w h₀) (j.castAdd 4)≠0) (i : ℕ) :
    QRegular p h₀ (fun h => PadeRatioWitness318.fill (w h) (construct (w h)) i) := by
  have hf := FV p h₀ w hw
  have hp := polynomial p h₀ w hw hG
  have hc := common p h₀ w hw hG hB
  have hj (j : Fin 4) := alternate p h₀ w hw j (hJ j)
  have hl (j : Fin 4) := primary p h₀ w hw j (hv j)
  have hr (j : Fin 4) := alternateRatio p h₀ w hw j hG hB hC (hJ j)
  unfold PadeRatioWitness318.fill
  split <;> index_regularity

/-- The actual h≠0,1 producer supplies all Padé/log domains. No ratio,
logarithm or nonsplitting domain is assumed at every later h. -/
theorem actual
    (hb : ∀ e : ℕ, ∀ m : ℤ, ‖ActualOrbitLocalFilter318.error p (4*6^e*m)‖≤((p:ℝ)⁻¹)^e)
    (q : ℚ) (labels : Fin 4 → ℤ) (hzero : h₀≠0) (hone : h₀≠1)
    (hg : RealGuardWitness318.Guards (CoherentMultiplePrefix318.u labels h₀)) (i : ℕ) :
    QRegular p h₀ (fun h => ActualPadeRatios318.witness q labels h i) := by
  apply fill p h₀ (fun h => base q labels h)
    (PrefixLocalRegularity318.prefix p hb q labels h₀ hzero hg)
  · rw [base_arg]
    exact CompressedChartDomains318.denominator_ne _ _
  · rw [base_B]
    exact CompressedChartDomains318.anchorB_ne _ _
      (fun he => hzero ((CoherentMultipleCharts318.chartU_zero_iff _).mp he))
      (CoherentMultipleCharts318.chart_curve _)
  · rw [base_common]
    exact CompressedChartDomains318.actual_commonLog_ne h₀ hzero hone
  · intro j
    rw [base_v]
    exact CompressedChartDomains318.alternate_denominator_ne _
  · intro j
    rw [base_v]
    exact CoherentAdditionV318.chartV_ne _

end PadeLocalRegularity318
