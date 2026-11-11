module
public import RealDetectorCoefficients318
public section
noncomputable section
namespace RealPadeSourceBridge318
open CircuitReplay ConcreteG8Domain RealDetectorRatios318 RealDetectorCoefficients318
open RealQuarticAmbient318 ActualCyclicClosure318
open CoherentMultipleCharts318 CompressedChartDomains318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

lemma anchor_u_orbit (e : Fin 2) (h : ℤ) :
    ((pairOrbit h) e).val.1=embedding e (chartU h) := rfl
lemma anchor_v_orbit (e : Fin 2) (h : ℤ) :
    ((pairOrbit h) e).val.2=embedding e (chartV h) := rfl

lemma base_mid (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    CompressedOrientation318.mid (ActualPadeRatios318.base q labels h)=
      (chartU h)^2*CompressedAnchorWitness318.shiftWitness (chartU h) (chartV h) := by
  ext <;> simp [CompressedOrientation318.mid,ActualPadeRatios318.base,CoherentMultiplePrefix318.witness,
    RealGuardWitness318.fill,CompressedAnchorWitness318.fill,pair]

lemma base_A (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    PadeRatioWitness318.A (ActualPadeRatios318.base q labels h)=
      CompressedChartDomains318.anchorA (chartU h) (chartV h) := by
  unfold PadeRatioWitness318.A CompressedChartDomains318.anchorA
  rw [ActualPadeRatios318.base_shift,base_mid]
  ring

lemma primary_orbit (q : ℚ) (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2) (h : ℤ) :
    RealDetectorRatios318.primary labels j e (pairOrbit h)=
      embedding e ((ActualPadeRatios318.construct (ActualPadeRatios318.base q labels h)).primaryRatio j) := by
  simp only [RealDetectorRatios318.primary,ActualPadeRatios318.construct,
    ActualPadeRatios318.base_u,ActualPadeRatios318.base_v,base_A,
    map_div₀,map_mul,u_orbit,v_orbit,anchorA_orbit]

lemma alternatePolynomial_orbit (q : ℚ) (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2) (h : ℤ) :
    RealDetectorRatios318.alternatePolynomial labels j e (pairOrbit h)=
      embedding e ((ActualPadeRatios318.construct (ActualPadeRatios318.base q labels h)).alternatePolynomial j) := by
  simp only [RealDetectorRatios318.alternatePolynomial,ActualPadeRatios318.construct,
    ActualPadeRatios318.alternatePolynomial,ActualPadeRatios318.base_v]
  split_ifs <;> simp [v_orbit,Pade21Domains.PJ,Pade21Domains.QJ,map_div₀,map_sub,map_add,map_mul,map_pow,map_ofNat]

lemma alternate_orbit (q : ℚ) (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2) (h : ℤ) :
    RealDetectorRatios318.alternate labels j e (pairOrbit h)=
      embedding e ((ActualPadeRatios318.construct (ActualPadeRatios318.base q labels h)).alternateRatio j) := by
  simp only [RealDetectorRatios318.alternate,alternatePolynomial_orbit q labels,ActualPadeRatios318.construct,
    ActualPadeRatios318.base_u,ActualPadeRatios318.base_common,
    map_div₀,map_mul,map_neg,u_orbit,common_orbit]

lemma polynomial_orbit (q : ℚ) (labels : Fin 4 → ℤ) (e : Fin 2) (h : ℤ) :
    Pade21Domains.PG (RealDetectorRatios318.argument e (pairOrbit h))/
      Pade21Domains.QG (RealDetectorRatios318.argument e (pairOrbit h))=
      embedding e ((ActualPadeRatios318.construct (ActualPadeRatios318.base q labels h)).commonPolynomial) := by
  simp [ActualPadeRatios318.construct,ActualPadeRatios318.polynomial,ActualPadeRatios318.base_arg,
    argument_orbit,Pade21Domains.PG,Pade21Domains.QG,map_div₀,map_sub,map_add,map_mul,map_pow,map_ofNat]

lemma common_orbit_source (q : ℚ) (labels : Fin 4 → ℤ) (e : Fin 2) (h : ℤ) :
    RealDetectorRatios318.common e (pairOrbit h)=
      embedding e ((ActualPadeRatios318.construct (ActualPadeRatios318.base q labels h)).commonLog) := by
  simp only [ActualPadeRatios318.construct,ActualPadeRatios318.base_common,common_orbit]

lemma root_orbit (labels : Fin 4 → ℤ) (j : Fin 4) (e : Fin 2) (h : ℤ) :
    RealDetectorCoefficients318.root labels j e (pairOrbit h)=
      embedding e (RealGuardWitness318.root (CoherentMultiplePrefix318.u labels h)
        (CoherentMultiplePrefix318.v labels h) j) := by
  simp only [RealDetectorCoefficients318.root,RealGuardWitness318.root,RealGuardWitness318.numerator,
    RealGuardWitness318.denominator,map_div₀,map_sub,map_add,map_mul,map_pow,u_orbit,v_orbit]

lemma guard_orbit (labels : Fin 4 → ℤ) (j : Fin 4) (h : ℤ) :
    RealDetectorCoefficients318.guard labels j (pairOrbit h)=
      ((RealGuardWitness318.denominator (CoherentMultiplePrefix318.u labels h) j).re:ℝ) := by
  have he : (fun e => (u labels (j.natAdd 4) e (pairOrbit h))^2-
    (u labels (j.castAdd 4) e (pairOrbit h))^2)=
    fun e => embedding e (RealGuardWitness318.denominator (CoherentMultiplePrefix318.u labels h) j) := by
    funext e
    simp only [RealGuardWitness318.denominator,map_sub,map_pow,u_orbit]
  exact (congrArg RealDetectorRatios318.re he).trans (re_embedding _)

lemma fV_orbit_source (q : ℚ) (labels : Fin 4 → ℤ) (e : Fin 2) (h : ℤ) :
    RealDetectorRatios318.fV e (pairOrbit h)=embedding e
      (CompressedOrientation318.fV (ActualPadeRatios318.base q labels h)) := by
  rw [ActualPadeRatios318.base_fV]
  simp only [RealDetectorRatios318.fV,shift_orbit,map_mul,map_pow]
  rfl

/-- Exact coefficient comparison for every pre-detector slot, including the
unmodified input placeholders. No equality is asserted only on the rows. -/
theorem raw_orbit (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) (i : Fin 118) :
    RealDetectorCoefficients318.raw q labels (pairOrbit h) i.val=
      (ActualPadeRatios318.witness q labels h i.val:ℝ) := by
  fin_cases i <;>
    simp only [RealDetectorCoefficients318.raw,primary_orbit q labels,alternate_orbit q labels,
      alternatePolynomial_orbit q labels,polynomial_orbit q labels,common_orbit_source q labels,
      root_orbit,guard_orbit,u_orbit,v_orbit,shift_orbit,fV_orbit_source q labels,
      anchor_u_orbit,anchor_v_orbit,
      ←map_pow,←map_mul,re_embedding,im_embedding] <;>
    simp [ActualPadeRatios318.witness,PadeRatioWitness318.fill,ActualPadeRatios318.base,
      CoherentMultiplePrefix318.witness,RealGuardWitness318.fill,CompressedAnchorWitness318.fill,
      ReciprocalChartWitness318.fill,ActualPadeRatios318.construct,
      RealDetectorRatios318.re,RealDetectorRatios318.im,pairOrbit,RealCoherentOrbit318.orbit,
      embedding,ActualQuadraticEmbeddings318.positiveEmbedding,
      ActualQuadraticEmbeddings318.negativeEmbedding,ActualQuadraticEmbeddings318.realEmbedding_pair,
      CoherentMultiplePrefix318.u,CoherentMultiplePrefix318.v] <;>
    push_cast <;> ring

end RealPadeSourceBridge318
