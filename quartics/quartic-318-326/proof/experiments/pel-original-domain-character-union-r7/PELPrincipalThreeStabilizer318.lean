module
public import QuaternionicFixedParameter318
public import PELJointNormOneAction318
public import PELIntegralOverorder318
public section
noncomputable section
namespace PELPrincipalThreeStabilizer318
open QuaternionicRealPeriod318 QuaternionicMobiusPeriods318 QuaternionicFixedParameter318
open QuaternionicUnitPeriodTransport318 PELQuaternionAlgebra318 PELQuaternionRealRepresentation318
open PELPrincipalOrderCoordinates318 PELPeriodDeterminant318
set_option maxHeartbeats 1400000

theorem representation_trace (x : B) :
    representation x 0 0+representation x 1 1=(reducedTrace x:ℝ) := by
  change (x.re:ℝ)+beta*(x.imJ:ℝ)+((x.re:ℝ)-beta*(x.imJ:ℝ))=↑(2*x.re)
  push_cast
  ring

/-- Exact degree-two expansion at the ORIGINAL quaternion element. -/
theorem norm_one_add_three (x : B) :
    reducedNorm (1+(3:ℕ) • x)=1+3*reducedTrace x+9*reducedNorm x := by
  simp only [reducedNorm,reducedTrace,nsmul_eq_mul]
  norm_num
  <;> ring

theorem integer_small_norm (n : ℤ) (h : 9*(n:ℝ)^2≤4*(n:ℝ)) : n=0 := by
  have hn : 0≤(n:ℝ) := by nlinarith [sq_nonneg (n:ℝ)]
  have hnZ : 0≤n := by exact_mod_cast hn
  by_contra hne
  have h1Z : 1≤n := by omega
  have h1 : 1≤(n:ℝ) := by exact_mod_cast h1Z
  have hs : (n:ℝ)≤(n:ℝ)^2 := by nlinarith [sq_nonneg ((n:ℝ)-1)]
  nlinarith

/-- Principal-three freeness for the SAME original order. The congruence
condition is u=1+3v with v IN THAT ORDER, not a larger level containing it. -/
theorem fixed_implies_one (u : orderˣ) (hu : reducedNorm ((u:order):B)=1)
    (v : order) (hlevel : (u:order)=1+(3:ℕ) • v)
    (τ : ℂ) (hτ : 0<τ.im) (hfix : unitParameter representation order u τ=τ) : u=1 := by
  have hB : ((u:order):B)=1+(3:ℕ) • (v:B) := congrArg order.subtype hlevel
  have hM : unitMatrix representation order u=1+(3:ℕ) • representation (v:B) := by
    change representation ((u:order):B)=_
    rw [hB,map_add,map_one,map_nsmul]
  have hline : fixesLine (representation (v:B)) τ := by
    apply remove_identity_three
    rw [←hM]
    exact fixesLine_of_mobius _ τ
      (denominator_ne _ (normOne_determinant u hu) τ hτ) hfix
  have hnorm : 3*reducedTrace (v:B)+9*reducedNorm (v:B)=0 := by
    rw [hB,norm_one_add_three] at hu
    linarith
  obtain ⟨n,hn⟩ := PELIntegralOverorder318.order_norm_integral (v:B) v.property
  have htr : reducedTrace (v:B)= -3*(n:ℚ) := by rw [hn] at hnorm; linarith
  have hbound := trace_bound (representation (v:B)) τ hτ hline
  rw [representation_trace,representation_det,htr,hn] at hbound
  have hsmall : 9*(n:ℝ)^2≤4*(n:ℝ) := by push_cast at hbound; nlinarith
  have hn0 := integer_small_norm n hsmall
  have hdet0 : (representation (v:B)).det=0 := by
    rw [representation_det,hn,hn0]
    all_goals norm_num
  have hvM := zero_of_det_zero (representation (v:B)) τ hτ hline hdet0
  have hvB : (v:B)=0 := representation_injective (hvM.trans (map_zero representation).symm)
  have hv : v=0 := Subtype.ext hvB
  apply Units.ext
  rw [hlevel,hv,smul_zero,add_zero]
end PELPrincipalThreeStabilizer318
