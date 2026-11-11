module
public import CoherentAdditionV318
public import CompressedAnchorWitness318
public import CompressedGlobal318
public import Pade21Domains
public section
noncomputable section
namespace CompressedChartDomains318
open ConcreteG8Domain (K)
open CompressedOrientation318 (D k m)
open CompressedAnchorWitness318 (shiftWitness)
open CompressedPoint318 (constant_equation k_ne)
open CoherentMultipleCharts318 (chartU chartV chart_curve chart_point)
open Pade21Domains
open scoped QuadraticAlgebra
set_option maxHeartbeats 2000000

@[expose] def anchorA (u v : K) : K := m+(k^2+D*u^2)*shiftWitness u v
@[expose] def anchorB (u v : K) : K := k^2+m*shiftWitness u v+D*u^2*(shiftWitness u v)^2
@[expose] def argument (u v : K) : K := D*(u^2*(shiftWitness u v)^2)^2
@[expose] def commonLog (u v : K) : K :=
  (k*shiftWitness u v/anchorB u v)*(PG (argument u v)/QG (argument u v))

lemma anchorA_eq (u v : K) : anchorA u v=k*v/u :=
  CompressedAnchorWitness318.ordinate_identity u v

lemma anchorB_ne (u v : K) (hu : u≠0) (hc : v^2=1-D*u^4) : anchorB u v≠0 := by
  have hb := CompressedGlobal318.compression_B_identity (u^2) (shiftWitness u v) k m D
    constant_equation (CompressedAnchorWitness318.compression_equation u v hu hc)
  have hn : QuadraticAlgebra.norm (u^2*(shiftWitness u v)^2)=
      (QuadraticAlgebra.norm (u*shiftWitness u v))^2 := by
    simp only [map_mul,map_pow]
    ring
  intro he
  change u^2*(anchorB u v)^2=k^2*(1-D*(u^2)^2*(shiftWitness u v)^4) at hb
  rw [he,zero_pow (by decide : 2≠0),mul_zero] at hb
  apply CompressedGlobal318.norm_square_obstruction _ _ hn
  have hz := (mul_eq_zero.mp hb.symm).resolve_left (pow_ne_zero 2 k_ne)
  linear_combination -hz

lemma argument_square (u v : K) :
    argument u v=(ConcreteG8Domain.pair 3 (-1)*(u^2*(shiftWitness u v)^2))^2 := by
  have hd : (ConcreteG8Domain.pair 3 (-1))^2=D := by
    ext <;> norm_num [D,ConcreteG8Domain.pair,pow_two]
  rw [mul_pow,hd]
  rfl

lemma denominator_ne (u v : K) : QG (argument u v)≠0 := by
  rw [argument_square]
  exact QG_nonzero_on_square _

lemma commonLog_ne (u v : K) (hu : u≠0) (hs : shiftWitness u v≠0)
    (hc : v^2=1-D*u^4) : commonLog u v≠0 :=
  mul_ne_zero (div_ne_zero (mul_ne_zero k_ne hs) (anchorB_ne u v hu hc))
    (div_ne_zero (PG_nonzero _) (denominator_ne u v))

/-- The compression parameter's identity branch is exactly the original
elliptic generator. This is proved on actual charts, without full-source
constraints or an assumed denominator fact. -/
theorem shift_chart_ne (h : ℤ) (hzero : h≠0) (hone : h≠1) :
    shiftWitness (chartU h) (chartV h)≠0 := by
  have hu : chartU h≠0 := fun he => hzero ((CoherentMultipleCharts318.chartU_zero_iff h).mp he)
  intro hs
  have hc := CompressedAnchorWitness318.compression_equation (chartU h) (chartV h) hu (chart_curve h)
  rw [hs] at hc
  have hx : 1/(chartU h)^2=k^2 := by
    apply (div_eq_iff (pow_ne_zero 2 hu)).mpr
    simpa using hc
  have hv := CompressedAnchorWitness318.ordinate_identity (chartU h) (chartV h)
  rw [hs] at hv
  have hy : chartV h/(chartU h)^3=k*m := by
    have hv' : m*chartU h=k*chartV h := by
      apply (eq_div_iff hu).mp
      simpa using hv
    apply (div_eq_iff (pow_ne_zero 3 hu)).mpr
    have hc' : k^2*(chartU h)^2=1 := by simpa using hc.symm
    linear_combination -(chartV h)*hc' - k*(chartU h)^2*hv'
  have hp := chart_point h
  have he : PrimaryFormal318.point (chartU h) (chartV h)
      (ReciprocalDifference318.ordinate_ne _ _ (chart_curve h)) (chart_curve h)=
      CompressedTranslation318.P := by
    rw [PrimaryFormal318.point,dif_neg hu,CompressedTranslation318.P,
      WeierstrassCurve.Affine.Point.some.injEq]
    exact ⟨hx,hy⟩
  have hgen : h • LocalGenerator318.P=LocalGenerator318.P :=
    hp.symm.trans ((congrArg (CompressedGeneratorBridge318.transport
      CompressedGeneratorBridge318.curve_eq) he).trans CompressedGeneratorBridge318.generator_eq)
  apply GeneratorMultiplesTwo318.generator_infinite_order (h-1) (sub_ne_zero.mpr hone)
  rw [sub_zsmul,one_zsmul,hgen,add_neg_cancel]

/-- Every divisor in the common alternate Padé logarithm is nonzero on
all selected original charts with h distinct from zero and one. -/
theorem actual_commonLog_ne (h : ℤ) (hzero : h≠0) (hone : h≠1) :
    commonLog (chartU h) (chartV h)≠0 :=
  commonLog_ne _ _
    (fun he => hzero ((CoherentMultipleCharts318.chartU_zero_iff h).mp he))
    (shift_chart_ne h hzero hone) (chart_curve h)

/-- All alternate J denominators are discharged on the actual coherent
charts, including identity charts; no arbitrary square argument is used. -/
lemma alternate_denominator_ne (n : ℤ) : QJ (chartV n-1)≠0 := by
  apply QJ_nonzero_on_circle (chartV n) (ConcreteG8Domain.pair 3 (-1)*(chartU n)^2)
  have hd : (ConcreteG8Domain.pair 3 (-1))^2=D := by
    ext <;> norm_num [D,ConcreteG8Domain.pair,pow_two]
  rw [mul_pow,hd]
  have hc := chart_curve n
  linear_combination hc

lemma alternate_numerator_ne (n : ℤ) : PJ (chartV n-1)≠0 := PJ_nonzero _

/-- The lower-order first alternate polynomial is nonzero on the original
quartic oval as well. -/
lemma first_alternate_polynomial_ne (n : ℤ) : 1-(chartV n-1)/5≠0 := by
  intro hz
  have hv : chartV n=6 := by linear_combination -5*hz
  have hc := chart_curve n
  rw [hv] at hc
  apply square_not_negative (-35) (by norm_num)
    (ConcreteG8Domain.pair 3 (-1)*(chartU n)^2)
  have hd : (ConcreteG8Domain.pair 3 (-1))^2=D := by
    ext <;> norm_num [D,ConcreteG8Domain.pair,pow_two]
  rw [mul_pow,hd]
  norm_num at hc ⊢
  linear_combination hc

end CompressedChartDomains318
