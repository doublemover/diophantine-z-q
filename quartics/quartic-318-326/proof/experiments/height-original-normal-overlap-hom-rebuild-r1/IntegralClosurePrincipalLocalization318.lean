module
public import IntegralClosureLocalizationMap318
public section
noncomputable section
namespace IntegralClosurePrincipalLocalization318
variable {P Q B : Type*} [CommRing P] [CommRing Q] [CommRing B]
  [Algebra P Q] [Algebra P B] [Algebra Q B] [IsScalarTower P Q B]
  (s : P) [IsLocalization.Away s Q]
local notation "N" => integralClosure P B
local notation "O" => integralClosure Q B
local instance : Algebra N O := IntegralClosureLocalizationMap318.normalAlgebra

/-- Clear a power of the actual base coordinate for EVERY normal element.
No finite-free, étale or branch-denominator hypothesis is needed. -/
lemma denominator (z : O) :
    ∃ n : ℕ, IsIntegral P (algebraMap P B s^n*z.val) := by
  obtain ⟨⟨m,k,hk⟩,hm⟩ :=
    IsIntegral.exists_multiple_integral_of_isLocalization
      (R:=P) (Rₘ:=Q) (Submonoid.powers s) z.val z.property
  refine ⟨k,?_⟩
  simpa only [←hk,Submonoid.smul_def,Algebra.smul_def,map_pow] using hm

/-- The full integral closure over the punctured base is the actual
principal localization of the old normal order inside the same B. -/
lemma localization : IsLocalization.Away (algebraMap P N s) O := by
  apply IsLocalization.Away.mk
  · have hu := (IsLocalization.Away.algebraMap_isUnit (S:=Q) s).map
      (algebraMap Q O)
    have he : algebraMap N O (algebraMap P N s)=
        algebraMap Q O (algebraMap P Q s) :=
      IntegralClosureLocalizationMap318.scalar_square s
    exact he.symm ▸ hu
  · intro z
    obtain ⟨n,hn⟩ := denominator s z
    refine ⟨n,⟨algebraMap P B s^n*z.val,hn⟩,?_⟩
    apply Subtype.ext
    change z.val*algebraMap P B s^n=algebraMap P B s^n*z.val
    exact mul_comm _ _
  · intro x y h
    have he : x=y := IntegralClosureLocalizationMap318.inclusion_injective h
    exact ⟨0,by rw [he]⟩
end IntegralClosurePrincipalLocalization318
