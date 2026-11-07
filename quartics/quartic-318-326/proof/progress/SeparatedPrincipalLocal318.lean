module
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace SeparatedPrincipalLocal318
set_option maxHeartbeats 600000
open Ideal IsLocalRing
variable {R:Type*} [CommRing R] [IsLocalRing R]
  [IsHausdorff (maximalIdeal R) R]

/-- A separated local ring with principal maximal ideal has the actual
unit-times-power decomposition, before any domain premise is imposed. -/
theorem decomposition (p:R) (hm:maximalIdeal R=Ideal.span {p}) {x:R} (hx:x≠0) :
    ∃n:ℕ,∃u:Rˣ,x=(u:R)*p^n := by
  classical
  have he:∃n:ℕ,x∉maximalIdeal R^n := by
    by_contra h
    push_neg at h
    apply hx
    apply IsHausdorff.haus' (I:=maximalIdeal R)
    intro n
    simpa only [SModEq.zero,smul_eq_mul,←Ideal.one_eq_top,mul_one] using h n
  have hn0:Nat.find he≠0 := by
    intro h
    have hh:=Nat.find_spec he
    rw [h,pow_zero,Ideal.one_eq_top] at hh
    exact hh (by trivial)
  obtain ⟨n,hn⟩:=Nat.exists_eq_succ_of_ne_zero hn0
  have hxin:x∈maximalIdeal R^n := by
    exact not_not.mp (Nat.find_min he (by omega))
  have hxout:x∉maximalIdeal R^(n+1) := by
    simpa only [hn] using Nat.find_spec he
  rw [hm,Ideal.span_singleton_pow,Ideal.mem_span_singleton] at hxin
  obtain ⟨y,hy⟩:=hxin
  have hyunit:IsUnit y := by
    by_contra h
    have hym:y∈maximalIdeal R := by simpa only [mem_maximalIdeal,mem_nonunits_iff] using h
    apply hxout
    rw [hy,pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (by rw [hm];exact Ideal.subset_span (by simp)) n) hym
  obtain ⟨u,hu⟩:=hyunit
  exact ⟨n,u,by rw [hy,←hu,mul_comm]⟩

/-- Nonvanishing of the parameter powers upgrades this actual separated ring
to a domain; the conclusion is not a supplied completion-domain hypothesis. -/
theorem domain (p:R) (hm:maximalIdeal R=Ideal.span {p}) (hp:∀n:ℕ,p^n≠0) : IsDomain R := by
  have hn:Nontrivial R := ⟨⟨1,0,by simpa using hp 0⟩⟩
  letI:=hn
  have hz:NoZeroDivisors R:=⟨by
    intro x y hxy
    by_contra h
    push_neg at h
    obtain ⟨n,u,rfl⟩:=decomposition p hm h.1
    obtain ⟨m,v,rfl⟩:=decomposition p hm h.2
    have hh:((u*v:Rˣ):R)*p^(n+m)=0 := by
      rw [Units.val_mul,pow_add]
      convert hxy using 1 <;> ring
    have hpz:p^(n+m)=0 := (u*v).mul_right_eq_zero.mp hh
    exact hp (n+m) hpz⟩
  exact { hn,hz with }

theorem principal (p:R) (hm:maximalIdeal R=Ideal.span {p}) : IsPrincipalIdealRing R := by
  classical
  constructor
  intro I
  by_cases hI:I=⊥
  · subst I; infer_instance
  have he:∃n:ℕ,p^n∈I := by
    obtain ⟨x,hxI,hx⟩:=Submodule.exists_mem_ne_zero_of_ne_bot hI
    obtain ⟨n,u,hu⟩:=decomposition p hm hx
    refine ⟨n,?_⟩
    have hh:=I.mul_mem_left (↑(u⁻¹):R) hxI
    simpa only [hu,←mul_assoc,Units.inv_mul,mul_one,one_mul] using hh
  refine ⟨⟨p^(Nat.find he),?_⟩⟩
  apply le_antisymm
  · intro x hxI
    by_cases hx:x=0
    · simp [hx]
    obtain ⟨m,u,hu⟩:=decomposition p hm hx
    have hpm:p^m∈I := by
      have hh:=I.mul_mem_left (↑(u⁻¹):R) hxI
      simpa only [hu,←mul_assoc,Units.inv_mul,one_mul] using hh
    have hnm:Nat.find he≤m:=Nat.find_min' he hpm
    rw [Ideal.mem_span_singleton,hu]
    exact dvd_mul_of_dvd_right (pow_dvd_pow p hnm) _
  · apply Ideal.span_le.mpr
    intro x hx
    have hh:x=p^(Nat.find he):=Set.mem_singleton_iff.mp hx
    subst x
    exact Nat.find_spec he

end SeparatedPrincipalLocal318
