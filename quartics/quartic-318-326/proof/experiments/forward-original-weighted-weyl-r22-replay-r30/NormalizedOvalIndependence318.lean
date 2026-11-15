module
public import NormalizationRealEmbedding318
public import RealOvalNormalization318
public import RealCoherentOrbit318
public section
noncomputable section

/-! Join the two normalized real elliptic generators to the exact coherent
oval generators. No density theorem is assumed or asserted in this module. -/
namespace NormalizedOvalIndependence318
open ConcreteG8Domain (K D)
open NormalizingRadicals318 NormalizedPointSigns318 NormalizationInjection318
open NormalizedGeneratorIndependence318 NormalizationRealEmbedding318
open ActualQuadraticEmbeddings318 (positiveEmbedding negativeEmbedding)
open CoherentMultipleCharts318 (chartU chartV)
open ReciprocalDouble318 ShortCurveBaseChange318 RealQuarticGroup318
local instance : DecidableEq Both := Classical.decEq Both
local instance : DecidableEq ℝ := Classical.decEq ℝ
local instance positiveGroup : AddCommGroup (Oval (positiveEmbedding D)) :=
  group _ (RealCoherentOrbit318.real_D_pos positiveEmbedding)
local instance negativeGroup : AddCommGroup (Oval (negativeEmbedding D)) :=
  group _ (RealCoherentOrbit318.real_D_pos negativeEmbedding)
local instance targetGroup : AddCommGroup (Oval 1) := group 1 (by norm_num)
set_option maxHeartbeats 2000000

lemma positive_coefficient : positiveEmbedding D=alpha^4 := by
  have he := congrArg realEmbedding first_coefficient
  simpa only [map_pow,realEmbedding_base,realEmbedding_firstRoot] using he

lemma negative_coefficient : negativeEmbedding D=beta^4 := by
  have he := congrArg realEmbedding conjugate_coefficient
  simpa only [map_pow,realEmbedding_conjugateBase,realEmbedding_secondRoot] using he

@[expose] def positiveEquiv : Oval (positiveEmbedding D) ≃+ Oval 1 :=
  RealOvalNormalization318.ovalAddEquiv _ (RealCoherentOrbit318.real_D_pos positiveEmbedding)
    alpha alpha_pos positive_coefficient.symm

@[expose] def negativeEquiv : Oval (negativeEmbedding D) ≃+ Oval 1 :=
  RealOvalNormalization318.ovalAddEquiv _ (RealCoherentOrbit318.real_D_pos negativeEmbedding)
    beta beta_pos negative_coefficient.symm

@[expose] def firstOvalGenerator : Oval 1 := positiveEquiv (RealCoherentOrbit318.orbit positiveEmbedding 1)
@[expose] def secondOvalGenerator : Oval 1 := negativeEquiv (RealCoherentOrbit318.orbit negativeEmbedding 1)

lemma positive_at (n : ℤ) :
    positiveEquiv (RealCoherentOrbit318.orbit positiveEmbedding n)=n • firstOvalGenerator := by
  rw [RealCoherentOrbit318.orbit_zsmul]
  simp only [map_zsmul,firstOvalGenerator]

lemma negative_at (n : ℤ) :
    negativeEquiv (RealCoherentOrbit318.orbit negativeEmbedding n)=n • secondOvalGenerator := by
  rw [RealCoherentOrbit318.orbit_zsmul]
  simp only [map_zsmul,secondOvalGenerator]

private lemma transport_point {F : Type*} [Field F] [CharZero F] [DecidableEq F]
    (d d' u v : F) (h : d=d') (hv : v≠0)
    (hc : v^2=1-d*u^4) :
    transport (congrArg E h) (point d u v hv hc)=point d' u v hv (h ▸ hc) := by
  subst d'
  rfl

/-- Prove the base-change constructor identity over abstract fields before
specializing to the actual nested radical field. The actual real map is unchanged. -/
private lemma map_one_reciprocal {F L : Type*} [Field F] [Field L]
    [CharZero F] [CharZero L] [DecidableEq F] [DecidableEq L]
    (σ : F →+* L) (u v : F) (hv : v≠0) (hc : v^2=1-(1:F)*u^4) :
    ((transport (congrArg E σ.map_one)).toAddMonoidHom.comp (pointMap σ 1))
      (point 1 u v hv hc)=
      point 1 (σ u) (σ v)
        (fun h => hv (σ.injective (h.trans σ.map_zero.symm)))
        (by simpa only [map_pow,map_sub,map_one,map_mul] using congrArg σ hc) := by
  change transport (congrArg E σ.map_one) (pointMap σ 1 (point 1 u v hv hc)) = _
  rw [pointMap_reciprocal,transport_point] <;> simp only [map_one]

private lemma realPoint_reciprocal (u v : Both) (hv : v≠0)
    (hc : v^2=1-(1:Both)*u^4) :
    realPoint (point 1 u v hv hc)=
      point 1 (realEmbedding u) (realEmbedding v)
        (fun h => hv (realEmbedding.injective (h.trans realEmbedding.map_zero.symm)))
        (by simpa only [map_pow,map_sub,map_one,map_mul] using congrArg realEmbedding hc) := by
  exact map_one_reciprocal realEmbedding u v hv hc

lemma real_chartV_ne (σ : K →+* ℝ) (n : ℤ) : σ (chartV n)≠0 :=
  fun h => CoherentAdditionV318.chartV_ne n (σ.injective (h.trans σ.map_zero.symm))

@[expose] def firstPointAt (n : ℤ) : (E (1:ℝ)).Point :=
  point 1 (alpha*positiveEmbedding (chartU n)) (positiveEmbedding (chartV n))
    (real_chartV_ne positiveEmbedding n)
    (NormalizationInjection318.normalized_curve positiveEmbedding D alpha positive_coefficient
      (chartU n) (chartV n) (CoherentAdditionV318.chart_curve n))

@[expose] def secondPointAt (n : ℤ) : (E (1:ℝ)).Point :=
  point 1 (beta*negativeEmbedding (chartU n)) (negativeEmbedding (chartV n))
    (real_chartV_ne negativeEmbedding n)
    (NormalizationInjection318.normalized_curve negativeEmbedding D beta negative_coefficient
      (chartU n) (chartV n) (CoherentAdditionV318.chart_curve n))

lemma firstPointAt_eq (n : ℤ) : firstPointAt n=n • firstRealGenerator := by
  have he := CoherentAdditionV318.reciprocal_chart_point n
  have hm := congrArg (fun Q => realPoint (normalize base D firstRoot firstRoot_ne first_coefficient Q)) he
  rw [normalize_reciprocal,realPoint_reciprocal] at hm
  have hz : realPoint (normalize base D firstRoot firstRoot_ne first_coefficient
      (n • LocalGenerator318.P))=n • firstRealGenerator := by
    calc
      _ = realPoint (n • normalize base D firstRoot firstRoot_ne first_coefficient
          LocalGenerator318.P) := congrArg realPoint
            (map_zsmul (normalize base D firstRoot firstRoot_ne first_coefficient) n LocalGenerator318.P)
      _ = n • realPoint (normalize base D firstRoot firstRoot_ne first_coefficient
          LocalGenerator318.P) := map_zsmul realPoint n _
      _ = _ := rfl
  have hc : firstPointAt n=realPoint (normalize base D firstRoot firstRoot_ne first_coefficient
      (n • LocalGenerator318.P)) := by
    simpa only [firstPointAt,map_mul,realEmbedding_firstRoot,realEmbedding_base] using hm
  exact hc.trans hz

lemma secondPointAt_eq (n : ℤ) : secondPointAt n=n • secondRealGenerator := by
  have he := CoherentAdditionV318.reciprocal_chart_point n
  have hm := congrArg (fun Q => realPoint (normalize conjugateBase D secondRoot secondRoot_ne conjugate_coefficient Q)) he
  rw [normalize_reciprocal,realPoint_reciprocal] at hm
  have hz : realPoint (normalize conjugateBase D secondRoot secondRoot_ne conjugate_coefficient
      (n • LocalGenerator318.P))=n • secondRealGenerator := by
    calc
      _ = realPoint (n • normalize conjugateBase D secondRoot secondRoot_ne conjugate_coefficient
          LocalGenerator318.P) := congrArg realPoint
            (map_zsmul (normalize conjugateBase D secondRoot secondRoot_ne conjugate_coefficient)
              n LocalGenerator318.P)
      _ = n • realPoint (normalize conjugateBase D secondRoot secondRoot_ne conjugate_coefficient
          LocalGenerator318.P) := map_zsmul realPoint n _
      _ = _ := rfl
  have hc : secondPointAt n=realPoint (normalize conjugateBase D secondRoot secondRoot_ne conjugate_coefficient
      (n • LocalGenerator318.P)) := by
    simpa only [secondPointAt,map_mul,realEmbedding_secondRoot,realEmbedding_conjugateBase] using hm
  exact hc.trans hz

/-- Integer independence holds for the actual normalized coherent oval
generators. This conclusion is not a compact-group density theorem. -/
theorem oval_integer_relation (m n : ℤ)
    (h : m • firstOvalGenerator+n • secondOvalGenerator=0) : m=0 ∧ n=0 := by
  have he : positiveEquiv (RealCoherentOrbit318.orbit positiveEmbedding m)=
      -negativeEquiv (RealCoherentOrbit318.orbit negativeEmbedding n) := by
    rw [positive_at,negative_at]
    exact eq_neg_of_add_eq_zero_left h
  have hu := congrArg (fun p : Oval 1 => p.val.1) he
  have hv := congrArg (fun p : Oval 1 => p.val.2) he
  change alpha*positiveEmbedding (chartU m)= -(beta*negativeEmbedding (chartU n)) at hu
  change positiveEmbedding (chartV m)=negativeEmbedding (chartV n) at hv
  have hp : firstPointAt m= -secondPointAt n := by
    unfold firstPointAt secondPointAt
    simp only [hu,hv]
    exact point_negative 1 _ _ _ _
  rw [firstPointAt_eq,secondPointAt_eq] at hp
  apply real_integer_relation m n
  rw [hp,neg_add_cancel]

end NormalizedOvalIndependence318
