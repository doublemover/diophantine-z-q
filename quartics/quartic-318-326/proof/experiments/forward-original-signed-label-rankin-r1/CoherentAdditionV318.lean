module
public import CoherentAdditionU318
public section
noncomputable section
namespace CoherentAdditionV318
open ConcreteG8Domain (K D)
open LocalGenerator318 (E P)
open GlobalGeneratorPoints318 (R)
open CoherentMultipleCharts318 (chartU chartV)
open WeierstrassCurve.Affine
open ReciprocalGroup318 (sumU sumV)
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Affine addition is independent of the implementation of decidable equality.
The generic reciprocal theorem fixes a classical implementation internally;
the concrete quadratic field supplies its own. Their equality is proved here. -/
private lemma addition_decidableEq_irrel {F : Type*} [Field F]
    (W : WeierstrassCurve.Affine F) (d₁ d₂ : DecidableEq F) (Q S : W.Point) :
    (letI : DecidableEq F := d₁; Q+S) =
      (letI : DecidableEq F := d₂; Q+S) := by
  have hd : d₁=d₂ := Subsingleton.elim _ _
  subst d₂
  rfl

lemma chart_curve (n : ℤ) : (chartV n)^2=1-D*(chartU n)^4 := by
  simpa only [CoherentMultipleCharts318.D_eq] using CoherentMultipleCharts318.chart_curve n

lemma chartV_ne (n : ℤ) : chartV n≠0 :=
  ReciprocalDifference318.ordinate_ne _ _ (CoherentMultipleCharts318.chart_curve n)

lemma reciprocal_chart_point (n : ℤ) :
    ReciprocalDouble318.point D (chartU n) (chartV n) (chartV_ne n) (chart_curve n)=n • P := by
  have he := CoherentMultipleCharts318.chart_point n
  by_cases hu : chartU n=0
  · simpa [ReciprocalDouble318.point,PrimaryFormal318.point,hu] using he
  · simpa only [ReciprocalDouble318.point,PrimaryFormal318.point,dite_eq_right hu,
      CompressedGeneratorBridge318.transport_some] using he

lemma P_orbit_injective : Function.Injective (fun n : ℤ => n • P) := by
  intro m n he
  change m • P=n • P at he
  by_contra hmn
  apply RealMultiples318.multiple_P_nonzero (m-n) (sub_ne_zero.mpr hmn)
  rw [sub_zsmul,he,add_neg_cancel]

/-- Same-square normalization is proved from the actual nontorsion orbit,
not assumed for arbitrary points of the real oval. -/
lemma chart_same_square (n m : ℤ) (hs : (chartU n)^2=(chartU m)^2) :
    chartV n=chartV m := by
  by_cases hn : n=0
  · subst n
    have hm : m=0 := (CoherentMultipleCharts318.chartU_zero_iff m).mp (by simpa using hs.symm)
    subst m
    rfl
  by_cases hm : m=0
  · subst m
    have hz : n=0 := (CoherentMultipleCharts318.chartU_zero_iff n).mp (by simpa using hs)
    exact (hn hz).elim
  have hun : chartU n≠0 := fun h => hn ((CoherentMultipleCharts318.chartU_zero_iff n).mp h)
  have hum : chartU m≠0 := fun h => hm ((CoherentMultipleCharts318.chartU_zero_iff m).mp h)
  have hx : (n • P).xRep=(m • P).xRep := by
    rw [←reciprocal_chart_point n,←reciprocal_chart_point m,
      ReciprocalDouble318.point,dite_eq_right hun,ReciprocalDouble318.point,dite_eq_right hum]
    simp only [Point.xRep_some,hs]
  rcases Point.eq_or_eq_neg_of_xRep_eq_xRep hx with he|he
  · exact congrArg chartV (P_orbit_injective he)
  · have hn : n= -m := P_orbit_injective (by simpa only [neg_zsmul] using he)
    rw [hn,CoherentMultipleCharts318.chartV_negative]

lemma chartU_add (n m : ℤ) :
    chartU (n+m)=sumU D (chartU n) (chartV n) (chartU m) (chartV m) := by
  simp only [CoherentMultipleCharts318.chartU,CoherentMultipleCharts318.chartV,add_zsmul]
  exact CoherentAdditionU318.u_add _ _

/-- The same oriented V coordinate satisfies the full rational group law on
all actual integer multiples, including zero, tangent and inverse cases. -/
theorem chartV_add (n m : ℤ) :
    chartV (n+m)=sumV D (chartU n) (chartV n) (chartU m) (chartV m) := by
  have hc := chart_curve n
  have hd := chart_curve m
  have hq := CoherentRootSign318.addition_denominator_ne (chartU n) (chartU m)
  by_cases hzero : n+m=0
  · have hm : m= -n := by omega
    subst m
    rw [add_neg_cancel,CoherentMultipleCharts318.chartV_zero,
      CoherentMultipleCharts318.chartU_negative,CoherentMultipleCharts318.chartV_negative]
    unfold sumV
    apply (eq_div_iff (pow_ne_zero 2 (CoherentRootSign318.addition_denominator_ne (chartU n) (-chartU n)))).mpr
    linear_combination -(1-D*(chartU n)^4)*hc
  have houtcurve := ReciprocalGroup318.sum_curve D _ _ _ _ hc hd hq
  have hout : sumV D (chartU n) (chartV n) (chartU m) (chartV m)≠0 :=
    ReciprocalDifference318.ordinate_ne _ _ (by simpa only [CoherentMultipleCharts318.D_eq] using houtcurve)
  have he := ReciprocalGroup318.actual_add D (chartU n) (chartV n) (chartU m) (chartV m)
    (chartV_ne n) (chartV_ne m) hc hd
    (fun h => by rw [(CoherentMultipleCharts318.chartU_zero_iff n).mp h]; exact CoherentMultipleCharts318.chartV_zero)
    (fun h => by rw [(CoherentMultipleCharts318.chartU_zero_iff m).mp h]; exact CoherentMultipleCharts318.chartV_zero)
    (chart_same_square n m) hq hout
  -- Keep the reciprocal-field point type on both sides of this comparison.
  -- Rewriting local points inside the generic addition expression leaves a
  -- mixed commutative-ring instance spine; typed equality composition does not.
  have he' :
      ReciprocalDouble318.point D (chartU (n+m)) (chartV (n+m))
        (chartV_ne (n+m)) (chart_curve (n+m))=
      ReciprocalDouble318.point D (sumU D (chartU n) (chartV n) (chartU m) (chartV m))
        (sumV D (chartU n) (chartV n) (chartU m) (chartV m)) hout houtcurve := by
    calc
      _ = (n+m) • P := reciprocal_chart_point (n+m)
      _ = n • P+m • P := add_zsmul P n m
      _ = ReciprocalDouble318.point D (chartU n) (chartV n) (chartV_ne n) hc+
          ReciprocalDouble318.point D (chartU m) (chartV m) (chartV_ne m) hd :=
        congrArg₂ (fun Q S : E.Point => Q+S)
          (reciprocal_chart_point n).symm (reciprocal_chart_point m).symm
      _ = _ :=
        (addition_decidableEq_irrel (ReciprocalDouble318.E D)
          (inferInstance : DecidableEq K) _ _ _).trans he
  have hu : chartU (n+m)≠0 := fun h => hzero ((CoherentMultipleCharts318.chartU_zero_iff (n+m)).mp h)
  have hsum : sumU D (chartU n) (chartV n) (chartU m) (chartV m)≠0 := by
    rwa [←chartU_add] 
  simp only [ReciprocalDouble318.point,dite_eq_right hu,dite_eq_right hsum,Point.some.injEq] at he'
  have hy := he'.2
  rw [←chartU_add] at hy
  exact (div_left_inj' (pow_ne_zero 3 hu)).mp hy

end CoherentAdditionV318
