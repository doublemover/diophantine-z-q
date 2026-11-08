module
public import FifthCharacterShortPolynomial318
public import InfinityVietaAlgebra318
public section
noncomputable section
namespace FifthBranchEquation318
open Polynomial FifthCharacterShortPolynomial318
set_option maxHeartbeats 650000
@[expose] def branchFactor:ℚ[X]:=C (-74088)*(X-C 32)*(X-C 76832)*(X+C 343)
lemma quartic_factor : FifthCharacterPolynomial318.quartic=X*branchFactor:=by
  unfold FifthCharacterPolynomial318.quartic branchFactor
  ring
/-- Polynomial identity valid also at the omitted quartic branch t=0. -/
theorem infinity_identity : C (yScale:ℚ)^2*branchFactor=
    (C (xScale:ℚ)+C shift*X)^3+C A*(C (xScale:ℚ)+C shift*X)*X^2+C B*X^3:=by
  apply Polynomial.funext
  intro t
  norm_num [branchFactor,xScale,yScale,shift,A,B]
  ring
lemma branchFactor_zero : branchFactor.eval 0≠0:=by norm_num [branchFactor]

section Regular
variable {S:Type*} [CommRing S]
variable (m k a b t w:S) (n h:Sˣ)
variable (hw:w^2=t*(h:S))
variable (hp:(n:S)^2*(h:S)=(m+k*t)^3+a*(m+k*t)*t^2+b*t^3)
@[expose] def outU:S:=(m+k*t)*w*↑(n*h)⁻¹
@[expose] def outV:S:=t*w*↑(n*h)⁻¹
lemma outU_den : outU m k t w n h*↑(n*h)=(m+k*t)*w:=by
  rw [outU,mul_assoc,Units.inv_mul,mul_one]
lemma outV_den : outV t w n h*↑(n*h)=t*w:=by
  rw [outV,mul_assoc,Units.inv_mul,mul_one]
include hw hp in
/-- Exact infinity-chart equation over any commutative test algebra,
including nilpotents, using only the displayed genuine units. -/
theorem regular_equation :
    outV t w n h-(outU m k t w n h)^3-a*outU m k t w n h*(outV t w n h)^2-
      b*(outV t w n h)^3=0:=by
  apply (Units.mul_right_inj ((n*h)^3)).mp
  change (↑(n*h):S)^3*_=(↑(n*h):S)^3*0
  rw [mul_zero,mul_comm ((↑(n*h):S)^3)]
  calc
    _=(outV t w n h*↑(n*h))*(↑(n*h):S)^2-(outU m k t w n h*↑(n*h))^3-
      a*(outU m k t w n h*↑(n*h))*(outV t w n h*↑(n*h))^2-
      b*(outV t w n h*↑(n*h))^3:=by ring
    _=0:=by
      rw [outU_den,outV_den,Units.val_mul]
      linear_combination -(n:S)^2*(h:S)*w*hw+w^3*hp
end Regular
end FifthBranchEquation318
