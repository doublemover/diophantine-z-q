module
public import PELOriginalLevelThetaIndependence318
public import PELOriginalPolarizationPowerBundle318
public section
noncomputable section
namespace PELOriginalLevelPowerSections318
open QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalLevelTheta318 PELOriginalThetaGaugeMatrix318
open PELOriginalThetaHermitianGauge318 PELOriginalSiegelNormalization318
open PELOriginalGaugedTheta318 PELOriginalPolarizationAutomorphy318
open PELOriginalPolarizationTransitions318 PELOriginalPolarizationLineBundle318
open PELOriginalPolarizationPowerBundle318 PELOriginalThetaQuasiperiods318
variable (τ:ℂ) (hτ:0<τ.im) (N:ℕ) [NeZero N]
@[expose] def normalizedValue (r:Label N) (z:ComplexVectors):ℂ:=
  gauge (bilinearMap τ) z^N*levelTheta τ N r z
@[expose] def value (r:Label N) (z:ComplexVectors):ℂ:=
  normalizedValue τ N r (normalization τ hτ z)
lemma normalized_holomorphic (r:Label N):Differentiable ℂ (normalizedValue τ N r):=
  (((gauge_smooth τ).differentiable (by simp)).pow N).mul
    (PELOriginalLevelTheta318.holomorphic τ hτ N r)
lemma holomorphic (r:Label N):Differentiable ℂ (value τ hτ N r):=
  (normalized_holomorphic τ hτ N r).comp
    (normalization τ hτ).toContinuousLinearEquiv.differentiable
lemma normalized_automorphy (r:Label N) (p:PELOriginalSymplecticCoordinates318.Pair)
    (z:ComplexVectors):
    normalizedValue τ N r (z+standardPeriod τ p)=
      normalizedFactor τ hτ p z^N*normalizedValue τ N r z:=by
  rw [normalizedValue,PELOriginalLevelTheta318.original_period]
  rw [←mul_assoc,←mul_pow,exact_multiplier τ hτ (bilinearMap τ)
    (PELOriginalThetaGaugeMatrix318.symmetric τ) (period_difference τ hτ),mul_pow]
  rfl
lemma original_automorphy (r:Label N) (l:L τ hτ) (z:ComplexVectors):
    value τ hτ N r (z+l.val)=factor τ hτ l z^N*value τ hτ N r z:=by
  simp only [value,map_add,period_exact]
  rw [normalized_automorphy τ hτ N]
  simp only [normalizedFactor,LinearEquiv.symm_apply_apply,label_exact]

/-- N² explicit holomorphic sections of the N-th power of the SAME
original line cocycle. The exact original gauge and entire lattice are
preserved; these are not sections of accidentally flat-twisted translates. -/
@[expose] def levelSection (r:Label N) (q:Base τ):PowerTotal τ hτ N:=
  powerSection τ hτ N (value τ hτ N r) q
lemma continuous (r:Label N):Continuous (levelSection τ hτ N r):=
  continuous_section τ hτ N _ (holomorphic τ hτ N r).continuous
    (original_automorphy τ hτ N r)
lemma holomorphic_in_original_charts (r:Label N) (a:ComplexVectors):
    DifferentiableOn ℂ (fun z:ComplexVectors=>((powerCore τ hτ N).localTriv a
      (levelSection τ hτ N r (projection (P τ) z))).2) (chart τ hτ a).target:=
  holomorphic_section τ hτ N _ (holomorphic τ hτ N r)
    (original_automorphy τ hτ N r) a

/-- Independence survives the actual common nonzero gauge and original
linear normalization, not just abstract identification of a dimension. -/
theorem original_values_independent:LinearIndependent ℂ (value τ hτ N):=by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply (Fintype.linearIndependent_iff.mp
    (PELOriginalLevelThetaIndependence318.entire_independent τ hτ N)) c
  funext z
  have h:=congrFun hc ((normalization τ hτ).symm z)
  have he:gauge (bilinearMap τ) z^N*(∑r:Label N,c r*levelTheta τ N r z)=0:=by
    simpa [value,normalizedValue,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,
      mul_left_comm,mul_assoc] using h
  have hz:∑r:Label N,c r*levelTheta τ N r z=0:=
    (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (gauge_nonzero _ z))
  simpa only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply] using hz
/-- Independence of the actual section family in its original selected
fiber gauges. Passing from those gauges back to ANY covering point uses
the proved original action and its nonzero factor, not a chosen lift. -/
theorem sections_independent:
    LinearIndependent ℂ (fun r:Label N=>fun q:Base τ=>(levelSection τ hτ N r q).2):=by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro c hc
  apply (Fintype.linearIndependent_iff.mp (original_values_independent τ hτ N)) c
  funext z
  let q:Base τ:=projection (P τ) z
  let a:ComplexVectors:=(core τ hτ).indexAt q
  have ha:q∈baseSet τ hτ a:=(core τ hτ).mem_baseSet_at q
  let l:L τ hτ:=PELOriginalAutomorphyRepresentatives318.shiftTo τ hτ a z
  have hs:z+l.val=chart τ hτ a q:=by
    rw [l,PELOriginalAutomorphyRepresentatives318.shiftTo_value τ hτ a z ha]
    abel
  have hval:∑r:Label N,c r*value τ hτ N r (chart τ hτ a q)=0:=by
    simpa only [Finset.sum_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul,
      levelSection,powerSection] using congrFun hc q
  have he:factor τ hτ l z^N*(∑r:Label N,c r*value τ hτ N r z)=0:=by
    rw [←hs] at hval
    simp only [original_automorphy] at hval
    simpa only [Finset.mul_sum,mul_left_comm,mul_assoc] using hval
  have hz:∑r:Label N,c r*value τ hτ N r z=0:=
    (mul_eq_zero.mp he).resolve_left (pow_ne_zero _ (PELOriginalPolarizationAutomorphy318.nonzero τ hτ l z))
  simpa only [Finset.sum_apply,Pi.smul_apply,Pi.zero_apply,smul_eq_mul] using hz
end PELOriginalLevelPowerSections318
