module
public import PadeRatioWitness318
public section
noncomputable section
namespace ActualPadeRatios318
open ConcreteG8Domain (K pair)
open CircuitReplay Raw318FinalReplay
open CompressedOrientation318 (k m D shift mid fV)
open CoherentMultipleCharts318 (chartU chartV)
open PadeRatioWitness318 Pade21Domains
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
set_option maxRecDepth 100000

@[expose] def polynomial (w : Assignment) : K := PG (arg w)/QG (arg w)
@[expose] def common (w : Assignment) : K := k*shift w*polynomial w/B w
@[expose] def alternatePolynomial (w : Assignment) (j : Fin 4) : K :=
  if j=0 then 1-(v w 4-1)/5 else PJ (v w (j.natAdd 4)-1)/QJ (v w (j.natAdd 4)-1)

/-- Every Padé and ratio coordinate is an actual rational field formula. -/
@[expose] def construct (w : Assignment) : Data where
  commonPolynomial := polynomial w
  commonLog := common w
  alternatePolynomial := alternatePolynomial w
  primaryRatio j := u w (j.castAdd 4)*A w/(k*v w (j.castAdd 4))
  alternateRatio j := -u w (j.natAdd 4)*alternatePolynomial w j/common w

lemma construct_relations (w : Assignment)
    (hG : QG (arg w)≠0) (hB : B w≠0) (hC : common w≠0)
    (hJ : ∀ j : Fin 3, QJ (v w ⟨j.val+5,by omega⟩-1)≠0)
    (hv : ∀ j : Fin 4, v w (j.castAdd 4)≠0) : Relations w (construct w) := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · dsimp [construct,polynomial]
    field_simp [hG] <;> ring
  · dsimp [construct,common]
    field_simp [hB] <;> ring
  · simp [construct,alternatePolynomial]
  · intro j
    fin_cases j <;> norm_num [construct,alternatePolynomial] <;>
      field_simp [hJ 0,hJ 1,hJ 2] <;> ring
  · intro j
    dsimp [construct]
    field_simp [CompressedPoint318.k_ne,hv j] <;> ring
  · intro j
    dsimp [construct]
    field_simp [hC] <;> ring

@[expose] def base (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) : Assignment :=
  CoherentMultiplePrefix318.witness q labels h

lemma base_u (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (j : Fin 8) :
    u (base q labels h) j=CoherentMultiplePrefix318.u labels h j := by
  fin_cases j <;> ext <;>
    simp [u,base,CoherentMultiplePrefix318.witness,RealGuardWitness318.fill,
      CompressedAnchorWitness318.fill,ReciprocalChartWitness318.fill,pair]

lemma base_v (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (j : Fin 8) :
    v (base q labels h) j=CoherentMultiplePrefix318.v labels h j := by
  fin_cases j <;> ext <;>
    simp [v,base,CoherentMultiplePrefix318.witness,RealGuardWitness318.fill,
      CompressedAnchorWitness318.fill,ReciprocalChartWitness318.fill,pair]

lemma base_shift (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    shift (base q labels h)=CompressedAnchorWitness318.shiftWitness (chartU h) (chartV h) := by
  ext <;> simp [shift,base,CoherentMultiplePrefix318.witness,RealGuardWitness318.fill,
    CompressedAnchorWitness318.fill,pair]

lemma base_fV (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    fV (base q labels h)=(chartU h)^2*(CompressedAnchorWitness318.shiftWitness (chartU h) (chartV h))^2 := by
  ext <;> simp [fV,base,CoherentMultiplePrefix318.witness,RealGuardWitness318.fill,
    CompressedAnchorWitness318.fill,pair]

lemma base_B (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    B (base q labels h)=CompressedChartDomains318.anchorB (chartU h) (chartV h) := by
  unfold B CompressedChartDomains318.anchorB
  rw [base_shift,base_fV]
  ring

lemma base_arg (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    arg (base q labels h)=CompressedChartDomains318.argument (chartU h) (chartV h) := by
  unfold arg CompressedChartDomains318.argument
  rw [base_fV]

lemma base_common (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    common (base q labels h)=CompressedChartDomains318.commonLog (chartU h) (chartV h) := by
  unfold common polynomial CompressedChartDomains318.commonLog
  rw [base_shift,base_arg,base_B]
  ring

/-- All division hypotheses are produced from original coherent charts. The
exception h=1 is the actual H-P identity branch, excluded by choosing h>1. -/
theorem actual_relations (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ)
    (hzero : h≠0) (hone : h≠1) : Relations (base q labels h) (construct (base q labels h)) := by
  apply construct_relations
  · rw [base_arg]
    exact CompressedChartDomains318.denominator_ne _ _
  · rw [base_B]
    exact CompressedChartDomains318.anchorB_ne _ _
      (fun he => hzero ((CoherentMultipleCharts318.chartU_zero_iff h).mp he))
      (CoherentMultipleCharts318.chart_curve h)
  · rw [base_common]
    exact CompressedChartDomains318.actual_commonLog_ne h hzero hone
  · intro j
    rw [base_v]
    exact CompressedChartDomains318.alternate_denominator_ne _
  · intro j
    rw [base_v]
    exact CoherentAdditionV318.chartV_ne _

@[expose] def witness (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) : Assignment :=
  fill (base q labels h) (construct (base q labels h))

lemma witness_input (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) : witness q labels h 0=q := by
  rw [witness,fill_input]
  exact CoherentMultiplePrefix318.witness_input q labels h

/-- A single actual common-index assignment now satisfies first79 rows,
including all genuine Padé and primary/alternate ratios. -/
theorem witness_first79 (S q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ)
    (hzero : h≠0) (hone : h≠1)
    (hg : ∀ j, RealGuardTrace318.guardValue (labels j) (h • LocalGenerator318.P)≠0) :
    Constraints ((stage0 S).take 79) (witness q labels h) :=
  first79 S _ _ (CoherentMultiplePrefix318.witness_rows S q labels h hzero hg)
    (actual_relations q labels h hzero hone)

end ActualPadeRatios318
