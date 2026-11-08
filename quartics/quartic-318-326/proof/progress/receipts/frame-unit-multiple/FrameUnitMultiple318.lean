module
public import RegularUnitMultiple318
public section
noncomputable section
namespace FrameUnitMultiple318
variable {K V:Type*} [CommRing K] [AddCommGroup V] [Module K V]
/-- A regular coordinate divisor in a framed module gives a regular
multiple of a vector whose coefficient is exactly a unit times that divisor. -/
theorem multiple (e:V≃ₗ[K]K) (t k:K) (ω ω₀:V) (hk:IsUnit k)
    (h:t∣e ω) (h₀:e ω₀=k*t):∃a:K,ω=a • ω₀:=by
  obtain ⟨a,ha⟩:=h
  have hω:ω=(t*a) • e.symm 1:=by
    apply e.injective
    rw [map_smul,e.apply_symm_apply,smul_eq_mul,mul_one]
    exact ha
  have hξ:ω₀=(k*t) • e.symm 1:=by
    apply e.injective
    rw [map_smul,e.apply_symm_apply,smul_eq_mul,mul_one]
    exact h₀
  exact RegularUnitMultiple318.of_factorizations t a k ω ω₀ (e.symm 1) hk hω hξ
/-- A previously proved regular vector factorization suffices, without
rechecking the geometric action that supplied it. -/
theorem of_factorization (e:V≃ₗ[K]K) (t k:K) (ω ω₀ d:V) (hk:IsUnit k)
    (hd:e d=1) (h:∃a:K,ω=(t*a) • d) (h₀:e ω₀=k*t):∃a:K,ω=a • ω₀:=by
  apply multiple e t k ω ω₀ hk _ h₀
  obtain ⟨a,ha⟩:=h
  refine ⟨a,?_⟩
  rw [ha,map_smul,hd,smul_eq_mul,mul_one]
end FrameUnitMultiple318
