module
public import PELNormOneTraceObstruction318
public section
noncomputable section
namespace PELNormOneBaseStabilizer318
open QuaternionicRealPeriod318 QuaternionicMobiusPeriods318 QuaternionicFixedParameter318
open QuaternionicUnitPeriodTransport318 PELQuaternionAlgebra318 PELQuaternionRealRepresentation318
open PELPrincipalOrderCoordinates318 PELPeriodDeterminant318 PELPrincipalThreeStabilizer318
open PELNormOneTraceObstruction318
set_option maxHeartbeats 1500000

/-- Equality in the fixed-line trace bound forces the ORIGINAL matrix to
be scalar. The parameter remains in the upper half-plane throughout. -/
theorem scalar_of_extreme_trace (M : RealMatrices) (τ : ℂ) (hτ : 0<τ.im)
    (hf : fixesLine M τ) (hd : M.det=1) (e : ℝ) (he : e^2=1)
    (ht : M 0 0+M 1 1=2*e) : M=e • (1:RealMatrices) := by
  obtain ⟨ha,hb⟩ := coordinate_relations M τ hτ hf
  have hs := determinant_squares M τ hτ hf
  rw [hd] at hs
  have hm : M 1 1+M 1 0*τ.re=e := by linarith
  rw [hm,he] at hs
  have hc : M 1 0*τ.im=0 := by nlinarith [sq_nonneg (M 1 0*τ.im)]
  have hc0 : M 1 0=0 := (mul_eq_zero.mp hc).resolve_right hτ.ne'
  have hd0 : M 1 1=e := by simpa only [hc0,zero_mul,add_zero] using hm
  have ha0 : M 0 0=e := by simpa only [hc0,hd0,mul_zero,zero_mul,add_zero] using ha
  have hb0 : M 0 1=0 := by simpa only [hc0,neg_zero,zero_mul] using hb
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.smul_apply,Matrix.one_apply,ha0,hb0,hc0,hd0]

/-- The entire original norm-one order-unit stabilizer is exactly scalar
signs. No torsion classification or maximal-level curve model is assumed. -/
theorem fixed_implies_sign (u : orderˣ) (hu : reducedNorm ((u:order):B)=1)
    (τ : ℂ) (hτ : 0<τ.im) (hf : unitParameter representation order u τ=τ) :
    u=1 ∨ u= -1 := by
  have hd := normOne_determinant u hu
  have hl : fixesLine (unitMatrix representation order u) τ :=
    fixesLine_of_mobius _ τ (denominator_ne _ hd τ hτ) hf
  have hb := trace_bound (unitMatrix representation order u) τ hτ hl
  rw [hd] at hb
  have hb' : (reducedTrace ((u:order):B):ℝ)^2≤4 := by
    change (representation ((u:order):B) 0 0+representation ((u:order):B) 1 1)^2≤4*1 at hb
    rw [representation_trace] at hb
    simpa only [mul_one] using hb
  rcases extreme_trace (u:order) hu hb' with ht | ht
  · have htr : unitMatrix representation order u 0 0+unitMatrix representation order u 1 1=2*1 := by
      change representation ((u:order):B) 0 0+representation ((u:order):B) 1 1= _
      rw [representation_trace,ht]
      norm_num
    have hm := scalar_of_extreme_trace _ τ hτ hl hd 1 (by norm_num) htr
    have hb1 : ((u:order):B)=1 := by
      apply representation_injective
      simpa only [one_smul,map_one] using hm
    left
    apply Units.ext
    exact Subtype.ext hb1
  · have htr : unitMatrix representation order u 0 0+unitMatrix representation order u 1 1=2*(-1) := by
      change representation ((u:order):B) 0 0+representation ((u:order):B) 1 1= _
      rw [representation_trace,ht]
      norm_num
    have hm := scalar_of_extreme_trace _ τ hτ hl hd (-1) (by norm_num) htr
    have hb1 : ((u:order):B)= -1 := by
      apply representation_injective
      simpa only [neg_one_smul,map_neg,map_one] using hm
    right
    apply Units.ext
    exact Subtype.ext hb1
end PELNormOneBaseStabilizer318
