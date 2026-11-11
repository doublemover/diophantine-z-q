module
public import IntegralConductorNormalOpen318
public import ProperIdealComplexPoint318
public section
noncomputable section
namespace NormalFromPointwisePrincipalOpens318
open scoped nonZeroDivisors
variable (A : Type*) [CommRing A] [IsDomain A] [Algebra ℂ A]

/-- A fraction is regular if its denominator ideal is the whole ring.
This explicit ideal retains the SAME actual fraction field embedding. -/
@[expose] def denominatorIdeal (y : FractionRing A) : Ideal A where
  carrier := {a | ∃ b : A, algebraMap A (FractionRing A) a * y = algebraMap A (FractionRing A) b}
  zero_mem' := ⟨0,by simp⟩
  add_mem' := by
    rintro a c ⟨b,hb⟩ ⟨d,hd⟩
    exact ⟨b+d,by rw [map_add,add_mul,hb,hd,map_add]⟩
  smul_mem' := by
    rintro c a ⟨b,hb⟩
    refine ⟨c*b,?_⟩
    change algebraMap A (FractionRing A) (c*a) * y = _
    rw [map_mul,mul_assoc,hb,map_mul]

/-- Actual normal principal neighborhoods through every genuine complex
evaluation imply normality of the WHOLE original algebra. A hypothetical
proper denominator ideal has a complex point; a normal neighborhood at
that point then supplies a power of a nonvanishing denominator in that
ideal, an exact contradiction. No scheme-point density inference occurs. -/
theorem integrallyClosed
    (hpoints : ∀ I : Ideal A, I ≠ ⊤ → ∃ f : A →ₐ[ℂ] ℂ, ∀ a ∈ I, f a = 0)
    (hopens : ∀ f : A →ₐ[ℂ] ℂ, ∃ d : A,
      f d ≠ 0 ∧ IsIntegrallyClosed (Localization.Away d)) : IsIntegrallyClosed A := by
  apply (isIntegrallyClosed_iff (FractionRing A)).mpr
  intro y hy
  have htop : denominatorIdeal A y = ⊤ := by
    by_contra hn
    obtain ⟨f,hf⟩ := hpoints (denominatorIdeal A y) hn
    obtain ⟨d,hfd,hnormal⟩ := hopens f
    have hd : d ≠ 0 := fun hz => hfd (hz ▸ map_zero f)
    let M := Submonoid.powers d
    let B := Localization.Away d
    let K := FractionRing A
    have hM : M ≤ A⁰ := by
      rintro m ⟨n,rfl⟩
      exact mem_nonZeroDivisors_iff_ne_zero.mpr (pow_ne_zero n hd)
    let g : B →+* K := IsLocalization.map _ (T := A⁰) (RingHom.id A) hM
    letI : Algebra B K := g.toAlgebra
    letI : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq'
      (by rw [RingHom.algebraMap_toAlgebra,IsLocalization.map_comp,RingHomCompTriple.comp_eq])
    letI : IsFractionRing B K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization M B K
    have hyB : IsIntegral B y := hy.tower_top
    obtain ⟨b,hb⟩ := (isIntegrallyClosed_iff K).mp hnormal hyB
    obtain ⟨⟨a,m,hm⟩,he⟩ := IsLocalization.surj M b
    have hmy : algebraMap A K m * y = algebraMap A K a := by
      have h := congrArg (algebraMap B K) he
      rw [map_mul,←IsScalarTower.algebraMap_apply A B K,
        ←IsScalarTower.algebraMap_apply A B K,hb] at h
      exact (mul_comm _ _).trans h
    have hz : f m = 0 := hf m ⟨a,hmy⟩
    obtain ⟨n,rfl⟩ := hm
    rw [map_pow] at hz
    exact pow_ne_zero n hfd hz
  have hone : (1 : A) ∈ denominatorIdeal A y := by rw [htop]; trivial
  obtain ⟨a,ha⟩ := hone
  exact ⟨a,by simpa only [map_one,one_mul] using ha.symm⟩
end NormalFromPointwisePrincipalOpens318
