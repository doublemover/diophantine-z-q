module
public import CoherentRootSign318
public import ReciprocalGroup318
public section
noncomputable section
namespace CoherentAdditionU318
open ConcreteG8Domain (K D)
open LocalGenerator318 (E)
open CoherentMultipleCharts318 (u v)
open CompressedGeneratorBridge318 (transport curve_eq transport_some)
open WeierstrassCurve.Affine
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

lemma u_reciprocal (U V : K) (hV : V≠0)
    (hc : V^2=1-CompressedOrientation318.D*U^4) :
    u (transport curve_eq (PrimaryFormal318.point U V hV hc))=
      2*U*V/(1+D*U^4) := by
  by_cases hU : U=0
  · subst U
    simp [PrimaryFormal318.point]
  have hq : 1+D*U^4≠0 := by
    convert CoherentRootSign318.addition_denominator_ne U U using 1
    ring
  rw [PrimaryFormal318.point,dite_eq_right hU,transport_some]
  change 2*(V/U^3)/((1/U^2)^2+D)=2*U*V/(1+D*U^4)
  field_simp [hU,hq,CoherentMultipleCharts318.denominator_ne (1/U^2)]

/-- Exact tangent identity for the actual coherent half-point chart. -/
theorem u_double (Q : E.Point) :
    u (Q+Q)=ReciprocalGroup318.sumU D (u Q) (v Q) (u Q) (v Q) := by
  rw [←CoherentMultipleCharts318.point Q]
  rw [u_reciprocal,ReciprocalGroup318.sumU_double]
  rfl

/-- The actual coherent u coordinate respects addition on every point of the
original elliptic group. The equal-abscissa cases are treated explicitly. -/
theorem u_add (Q S : E.Point) :
    u (Q+S)=ReciprocalGroup318.sumU D (u Q) (v Q) (u S) (v S) := by
  by_cases hx : Q.xRep=S.xRep
  · rcases Point.eq_or_eq_neg_of_xRep_eq_xRep hx with he | he
    · subst S
      exact u_double Q
    · subst Q
      simp only [neg_add_cancel,CoherentMultipleCharts318.u_zero,
        CoherentMultipleCharts318.u_negative,CoherentMultipleCharts318.v_negative]
      simp [ReciprocalGroup318.sumU]
  · have hneg : Q.xRep≠(-S).xRep := by simpa only [Point.xRep_neg] using hx
    have he := CoherentRootSign318.u_sub_of_xRep_ne Q (-S) hneg
    simp only [sub_neg_eq_add,CoherentMultipleCharts318.u_negative,
      CoherentMultipleCharts318.v_negative,neg_sq,neg_mul,sub_neg_eq_add] at he
    exact (eq_div_iff (CoherentRootSign318.addition_denominator_ne _ _)).mpr he

end CoherentAdditionU318
