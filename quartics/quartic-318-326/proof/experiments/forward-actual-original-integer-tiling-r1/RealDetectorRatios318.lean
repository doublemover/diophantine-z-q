module
public import UniformPoleFamilies318
public import ActualPairDensity318
public section
noncomputable section
namespace RealDetectorRatios318
open ActualCyclicClosure318 RealQuarticAmbient318 CompressedOrientation318 Pade21Domains
open ConcreteG8Domain (K)
open scoped Topology
set_option maxHeartbeats 0

@[expose] def re (a : Fin 2 → ℝ) : ℝ := (a 0+a 1)/2
@[expose] def im (a : Fin 2 → ℝ) : ℝ := (a 0-a 1)/(2*Real.sqrt 2)

lemma re_embedding (a : K) : re (fun e => embedding e a)=(a.re:ℝ) := by
  rcases a with ⟨a,b⟩
  change re (fun e => embedding e (ConcreteG8Domain.pair a b))=_
  simp [re,embedding,ActualQuadraticEmbeddings318.positiveEmbedding,
    ActualQuadraticEmbeddings318.negativeEmbedding,ActualQuadraticEmbeddings318.realEmbedding_pair]
  <;> ring

lemma im_embedding (a : K) : im (fun e => embedding e a)=(a.im:ℝ) := by
  rcases a with ⟨a,b⟩
  change im (fun e => embedding e (ConcreteG8Domain.pair a b))=_
  simp only [im,embedding,ite_true,show (1:Fin 2)≠0 by decide,ite_false,
    ActualQuadraticEmbeddings318.positiveEmbedding,ActualQuadraticEmbeddings318.negativeEmbedding,
    ActualQuadraticEmbeddings318.realEmbedding_pair]
  field_simp [ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2))]
  <;> ring

@[expose] def chart (labels : Fin 4 → ℤ) (i : Fin 8) (X : Pair) : Pair :=
  Fin.append (fun j => labels j • X) (fun j => labels j • (X-generator)) i
@[expose] def u (labels : Fin 4 → ℤ) (i : Fin 8) (e : Fin 2) (X : Pair) : ℝ :=
  ((chart labels i X) e).val.1
@[expose] def v (labels : Fin 4 → ℤ) (i : Fin 8) (e : Fin 2) (X : Pair) : ℝ :=
  ((chart labels i X) e).val.2

lemma chart_continuous (labels : Fin 4 → ℤ) (i : Fin 8) : Continuous (chart labels i) := by
  refine Fin.addCases (m := 4) (n := 4) ?_ ?_ i
  · intro j
    change Continuous (fun X : Pair =>
      Fin.append (fun j => labels j • X) (fun j => labels j • (X-generator)) (j.castAdd 4))
    simpa only [Fin.append_left] using
      (show Continuous (fun X : Pair => labels j • X) by fun_prop)
  · intro j
    change Continuous (fun X : Pair =>
      Fin.append (fun j => labels j • X) (fun j => labels j • (X-generator)) (j.natAdd 4))
    simpa only [Fin.append_right] using
      (show Continuous (fun X : Pair => labels j • (X-generator)) by fun_prop)
@[fun_prop] lemma u_continuous (labels : Fin 4 → ℤ) (i : Fin 8) (e : Fin 2) : Continuous (u labels i e) := by
  exact (continuous_subtype_val.comp ((continuous_apply e).comp (chart_continuous labels i))).fst
@[fun_prop] lemma v_continuous (labels : Fin 4 → ℤ) (i : Fin 8) (e : Fin 2) : Continuous (v labels i e) := by
  exact (continuous_subtype_val.comp ((continuous_apply e).comp (chart_continuous labels i))).snd

lemma chart_orbit (labels : Fin 4 → ℤ) (i : Fin 8) (h : ℤ) :
    chart labels i (pairOrbit h)=pairOrbit (CoherentMultiplePrefix318.parameters labels h i) := by
  refine Fin.addCases (m := 4) (n := 4) ?_ ?_ i
  · intro j
    simpa only [chart,CoherentMultiplePrefix318.parameters,Fin.append_left] using
      ActualCyclicGuards318.scaled_orbit (labels j) h
  · intro j
    simpa only [chart,CoherentMultiplePrefix318.parameters,Fin.append_right] using
      ActualCyclicGuards318.shifted_orbit (labels j) h

lemma u_orbit (labels : Fin 4 → ℤ) (i : Fin 8) (e : Fin 2) (h : ℤ) :
    u labels i e (pairOrbit h)=embedding e (CoherentMultiplePrefix318.u labels h i) := by
  rw [u,chart_orbit]
  rfl
lemma v_orbit (labels : Fin 4 → ℤ) (i : Fin 8) (e : Fin 2) (h : ℤ) :
    v labels i e (pairOrbit h)=embedding e (CoherentMultiplePrefix318.v labels h i) := by
  rw [v,chart_orbit]
  rfl

@[expose] def shift (e : Fin 2) (X : Pair) : ℝ :=
  ((embedding e k)*(X e).val.2/(X e).val.1-embedding e m)/
    ((embedding e k)^2+d e*(X e).val.1^2)
@[expose] def fV (e : Fin 2) (X : Pair) : ℝ := (X e).val.1^2*(shift e X)^2
@[expose] def anchorA (e : Fin 2) (X : Pair) : ℝ :=
  embedding e m+((embedding e k)^2+d e*(X e).val.1^2)*shift e X
@[expose] def anchorB (e : Fin 2) (X : Pair) : ℝ :=
  (embedding e k)^2+(embedding e m)*shift e X+d e*fV e X
@[expose] def argument (e : Fin 2) (X : Pair) : ℝ := d e*(fV e X)^2
@[expose] def common (e : Fin 2) (X : Pair) : ℝ :=
  ((embedding e k)*shift e X/anchorB e X)*(PG (argument e X)/QG (argument e X))
@[expose] def alternatePolynomial (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2) (X : Pair) : ℝ :=
  if j=0 then 1-(v labels 4 e X-1)/5 else
    PJ (v labels (j.natAdd 4) e X-1)/QJ (v labels (j.natAdd 4) e X-1)
@[expose] def primary (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2) (X : Pair) : ℝ :=
  u labels (j.castAdd 4) e X*anchorA e X/((embedding e k)*v labels (j.castAdd 4) e X)
@[expose] def alternate (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2) (X : Pair) : ℝ :=
  -u labels (j.natAdd 4) e X*alternatePolynomial labels j e X/common e X

/-- The original quadratic coefficient in its two literal presentations. -/
lemma original_D_eq : ConcreteG8Domain.D = CompressedOrientation318.D := by
  ext <;> norm_num [ConcreteG8Domain.D,CompressedOrientation318.D,
    ConcreteG8Domain.i,ConcreteG8Domain.pair,pow_two,
    QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]

lemma shift_orbit (e : Fin 2) (h : ℤ) :
    shift e (pairOrbit h)=embedding e
      (CompressedAnchorWitness318.shiftWitness (CoherentMultipleCharts318.chartU h)
        (CoherentMultipleCharts318.chartV h)) := by
  simp only [shift,CompressedAnchorWitness318.shiftWitness,map_div₀,map_sub,map_mul,map_add,map_pow]
  simp only [pairOrbit,RealCoherentOrbit318.orbit,d,original_D_eq,mul_assoc]

lemma anchorA_orbit (e : Fin 2) (h : ℤ) :
    anchorA e (pairOrbit h)=embedding e
      (CompressedChartDomains318.anchorA (CoherentMultipleCharts318.chartU h)
        (CoherentMultipleCharts318.chartV h)) := by
  simp only [anchorA,CompressedChartDomains318.anchorA,map_add,map_mul,map_pow,shift_orbit]
  simp only [pairOrbit,RealCoherentOrbit318.orbit,d,original_D_eq,mul_assoc]

lemma anchorB_orbit (e : Fin 2) (h : ℤ) :
    anchorB e (pairOrbit h)=embedding e
      (CompressedChartDomains318.anchorB (CoherentMultipleCharts318.chartU h)
        (CoherentMultipleCharts318.chartV h)) := by
  simp only [anchorB,fV,CompressedChartDomains318.anchorB,map_add,map_mul,map_pow,shift_orbit]
  simp only [pairOrbit,RealCoherentOrbit318.orbit,d,original_D_eq,mul_assoc]

lemma argument_orbit (e : Fin 2) (h : ℤ) :
    argument e (pairOrbit h)=embedding e
      (CompressedChartDomains318.argument (CoherentMultipleCharts318.chartU h)
        (CoherentMultipleCharts318.chartV h)) := by
  simp only [argument,fV,CompressedChartDomains318.argument,map_mul,map_pow,shift_orbit]
  simp only [pairOrbit,RealCoherentOrbit318.orbit,d,original_D_eq,mul_assoc]

lemma common_orbit (e : Fin 2) (h : ℤ) :
    common e (pairOrbit h)=embedding e
      (CompressedChartDomains318.commonLog (CoherentMultipleCharts318.chartU h)
        (CoherentMultipleCharts318.chartV h)) := by
  simp only [common,CompressedChartDomains318.commonLog,map_mul,map_div₀,PG,QG,map_sub,map_pow,map_add,
    map_ofNat,map_one,shift_orbit,anchorB_orbit,argument_orbit]

lemma embedding_ne (e : Fin 2) {a : K} (ha : a≠0) : embedding e a≠0 := by
  intro hz
  exact ha ((embedding e).injective (by simpa using hz))

@[fun_prop] lemma pair_u_continuous (e : Fin 2) :
    Continuous (fun X : Pair => (X e).val.1) :=
  (continuous_subtype_val.comp (continuous_apply e)).fst
@[fun_prop] lemma pair_v_continuous (e : Fin 2) :
    Continuous (fun X : Pair => (X e).val.2) :=
  (continuous_subtype_val.comp (continuous_apply e)).snd

lemma shift_continuousAt (e : Fin 2) (X : Pair) (hu : (X e).val.1≠0) :
    ContinuousAt (shift e) X := by
  have hk : embedding e k≠0 := embedding_ne e CompressedPoint318.k_ne
  have hd : 0<d e := lt_trans zero_lt_one (d_gt_one e)
  have hden : (embedding e k)^2+d e*(X e).val.1^2≠0 := by
    have hp := sq_pos_of_ne_zero hk
    have hn := mul_nonneg (le_of_lt hd) (sq_nonneg (X e).val.1)
    exact ne_of_gt (by linarith)
  unfold shift
  exact (((continuousAt_const.mul (pair_v_continuous e).continuousAt).div
    (pair_u_continuous e).continuousAt hu).sub continuousAt_const).div
    (continuousAt_const.add (continuousAt_const.mul
      ((pair_u_continuous e).continuousAt.pow 2))) hden

lemma anchorA_continuousAt (e : Fin 2) (X : Pair) (hu : (X e).val.1≠0) :
    ContinuousAt (anchorA e) X := by
  unfold anchorA
  exact continuousAt_const.add
    ((continuousAt_const.add (continuousAt_const.mul
      ((pair_u_continuous e).continuousAt.pow 2))).mul (shift_continuousAt e X hu))
lemma fV_continuousAt (e : Fin 2) (X : Pair) (hu : (X e).val.1≠0) :
    ContinuousAt (fV e) X := by
  unfold fV
  exact ((pair_u_continuous e).continuousAt.pow 2).mul
    ((shift_continuousAt e X hu).pow 2)
lemma anchorB_continuousAt (e : Fin 2) (X : Pair) (hu : (X e).val.1≠0) :
    ContinuousAt (anchorB e) X := by
  unfold anchorB
  exact (continuousAt_const.add (continuousAt_const.mul (shift_continuousAt e X hu))).add
    (continuousAt_const.mul (fV_continuousAt e X hu))
lemma argument_continuousAt (e : Fin 2) (X : Pair) (hu : (X e).val.1≠0) :
    ContinuousAt (argument e) X := by
  unfold argument
  exact continuousAt_const.mul ((fV_continuousAt e X hu).pow 2)

lemma common_continuousAt (e : Fin 2) (X : Pair) (hu : (X e).val.1≠0)
    (hB : anchorB e X≠0) (hG : QG (argument e X)≠0) :
    ContinuousAt (common e) X := by
  have ha := argument_continuousAt e X hu
  unfold common
  apply ContinuousAt.mul
  · exact (continuousAt_const.mul (shift_continuousAt e X hu)).div
      (anchorB_continuousAt e X hu) hB
  · apply ContinuousAt.div
    · unfold PG
      exact (continuousAt_const.sub (continuousAt_const.mul ha)).add
        (continuousAt_const.mul (ha.pow 2))
    · unfold QG
      exact continuousAt_const.sub (continuousAt_const.mul ha)
    · exact hG

lemma alternatePolynomial_continuousAt (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2)
    (X : Pair) (hJ : QJ (v labels (j.natAdd 4) e X-1)≠0) :
    ContinuousAt (alternatePolynomial labels j e) X := by
  unfold alternatePolynomial
  split_ifs
  · exact (by fun_prop)
  · apply ContinuousAt.div
    · unfold PJ
      fun_prop (disch := assumption)
    · unfold QJ
      exact continuousAt_const.add (continuousAt_const.mul
        ((v_continuous labels (j.natAdd 4) e).continuousAt.sub continuousAt_const))
    · exact hJ

lemma primary_continuousAt (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2)
    (X : Pair) (hu : (X e).val.1≠0) (hv : v labels (j.castAdd 4) e X≠0) :
    ContinuousAt (primary labels j e) X := by
  unfold primary
  exact ((u_continuous labels (j.castAdd 4) e).continuousAt.mul
    (anchorA_continuousAt e X hu)).div
    (continuousAt_const.mul (v_continuous labels (j.castAdd 4) e).continuousAt)
    (mul_ne_zero (embedding_ne e CompressedPoint318.k_ne) hv)

lemma alternate_continuousAt (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2)
    (X : Pair) (hu : (X e).val.1≠0) (hB : anchorB e X≠0)
    (hG : QG (argument e X)≠0) (hJ : QJ (v labels (j.natAdd 4) e X-1)≠0)
    (hC : common e X≠0) : ContinuousAt (alternate labels j e) X := by
  unfold alternate
  exact ((u_continuous labels (j.natAdd 4) e).continuousAt.neg.mul
    (alternatePolynomial_continuousAt labels j e X hJ)).div
    (common_continuousAt e X hu hB hG) hC

/-- All real denominator domains at the original rational orbit are produced
from injectivity of both actual embeddings and the original chart lemmas. -/
lemma orbit_domains (labels : Fin 4 → ℤ) (h : ℤ) (h0 : h≠0) (h1 : h≠1) (e : Fin 2) :
    ((pairOrbit h) e).val.1≠0 ∧ anchorB e (pairOrbit h)≠0 ∧
    QG (argument e (pairOrbit h))≠0 ∧ common e (pairOrbit h)≠0 ∧
    ∀ j : Fin 4, v labels (j.castAdd 4) e (pairOrbit h)≠0 ∧
      QJ (v labels (j.natAdd 4) e (pairOrbit h)-1)≠0 := by
  have hu : CoherentMultipleCharts318.chartU h≠0 := by
    exact fun he => h0 ((CoherentMultipleCharts318.chartU_zero_iff h).mp he)
  refine ⟨embedding_ne e hu,?_,?_,?_,?_⟩
  · rw [anchorB_orbit]
    exact embedding_ne e (CompressedChartDomains318.anchorB_ne _ _ hu
      (CoherentMultipleCharts318.chart_curve h))
  · rw [argument_orbit]
    have he : QG (embedding e (CompressedChartDomains318.argument
      (CoherentMultipleCharts318.chartU h) (CoherentMultipleCharts318.chartV h)))=
      embedding e (QG (CompressedChartDomains318.argument
      (CoherentMultipleCharts318.chartU h) (CoherentMultipleCharts318.chartV h))) := by
      simp only [QG,map_sub,map_mul,map_div₀,map_ofNat,map_one]
    rw [he]
    exact embedding_ne e (CompressedChartDomains318.denominator_ne _ _)
  · rw [common_orbit]
    exact embedding_ne e (CompressedChartDomains318.actual_commonLog_ne h h0 h1)
  · intro j
    rw [v_orbit,v_orbit]
    constructor
    · exact embedding_ne e (CoherentAdditionV318.chartV_ne _)
    · have he : QJ (embedding e (CoherentMultiplePrefix318.v labels h (j.natAdd 4))-1)=
        embedding e (QJ (CoherentMultiplePrefix318.v labels h (j.natAdd 4)-1)) := by
        simp only [QJ,map_add,map_sub,map_mul,map_div₀,map_ofNat,map_one]
      rw [he]
      exact embedding_ne e (CompressedChartDomains318.alternate_denominator_ne _)

end RealDetectorRatios318
