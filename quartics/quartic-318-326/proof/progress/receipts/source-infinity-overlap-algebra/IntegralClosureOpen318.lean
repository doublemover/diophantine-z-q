module
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace IntegralClosureOpen318
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {R A B:Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
  (s:R) [hLoc : IsLocalization.Away s A] [hInt : Algebra.IsIntegral A B]

include hLoc hInt

/-- If the entire algebra is integral after inverting s on the base, it is
exactly the localization at s of its integral closure before inversion. No
fraction-field argument or surjectivity hypothesis is substituted for this
whole-ring localization statement. -/
theorem away_integralClosure :
    IsLocalization.Away (algebraMap R (integralClosure R B) s) B:=by
  apply IsLocalization.Away.mk
  · rw [←IsScalarTower.algebraMap_apply R (integralClosure R B) B,
      IsScalarTower.algebraMap_apply R A B]
    exact (IsLocalization.Away.algebraMap_isUnit (S:=A) s).map (algebraMap A B)
  · intro x
    obtain ⟨⟨_,n,rfl⟩,hn⟩:=IsIntegral.exists_multiple_integral_of_isLocalization
      (M:=Submonoid.powers s) (Rₘ:=A) x (Algebra.IsIntegral.isIntegral (R:=A) x)
    refine ⟨n,⟨s^n • x,hn⟩,?_⟩
    rw [←IsScalarTower.algebraMap_apply R (integralClosure R B) B]
    change x*(algebraMap R B s)^n=s^n • x
    rw [Algebra.smul_def,map_pow,mul_comm]
  · intro x y h
    have hxy:x=y:=Subtype.ext h
    exact ⟨0,by simpa only [pow_zero,one_mul] using hxy⟩
end IntegralClosureOpen318
