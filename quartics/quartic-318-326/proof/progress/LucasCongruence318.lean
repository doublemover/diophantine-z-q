module
public import ContactLeafData318
public import TorsionSafeIndex318
public section
namespace LucasCongruence318
set_option maxHeartbeats 0

section Algebra
variable {F:Type*} [Field F]

@[expose] def lucas (a b c:F) : F := b^2-a*(a-2)*b*c+(a-2)^2*c^2-1

/-- Simultaneous integrality and a common additive-valuation congruence. -/
@[expose] def IntegralClose (v:AddValuation F (WithTop ℤ)) (k:WithTop ℤ) (a b:F) : Prop :=
  0≤v a ∧ 0≤v b ∧ k≤v (a-b)

namespace IntegralClose
variable (v:AddValuation F (WithTop ℤ)) (k:WithTop ℤ)

theorem refl (a:F) (ha:0≤v a) : IntegralClose v k a a :=
  ⟨ha,ha,by simp⟩

theorem one : IntegralClose v k (1:F) 1 := refl v k 1 (by rw [v.map_one])

theorem add {a b c d:F} (hab:IntegralClose v k a b) (hcd:IntegralClose v k c d) :
    IntegralClose v k (a+c) (b+d) := by
  refine ⟨v.map_le_add hab.1 hcd.1,v.map_le_add hab.2.1 hcd.2.1,?_⟩
  convert v.map_le_add hab.2.2 hcd.2.2 using 1 <;> congr 1 <;> ring

theorem sub {a b c d:F} (hab:IntegralClose v k a b) (hcd:IntegralClose v k c d) :
    IntegralClose v k (a-c) (b-d) := by
  refine ⟨v.map_le_sub hab.1 hcd.1,v.map_le_sub hab.2.1 hcd.2.1,?_⟩
  convert v.map_le_sub hab.2.2 hcd.2.2 using 1 <;> congr 1 <;> ring

theorem mul {a b c d:F} (hab:IntegralClose v k a b) (hcd:IntegralClose v k c d) :
    IntegralClose v k (a*c) (b*d) := by
  have hac:0≤v (a*c) := by rw [v.map_mul]; exact add_nonneg hab.1 hcd.1
  have hbd:0≤v (b*d) := by rw [v.map_mul]; exact add_nonneg hab.2.1 hcd.2.1
  refine ⟨hac,hbd,?_⟩
  have hleft:k≤v ((a-b)*c) := by
    rw [v.map_mul]
    simpa only [add_zero] using add_le_add hab.2.2 hcd.1
  have hright:k≤v (b*(c-d)) := by
    rw [v.map_mul]
    simpa only [zero_add] using add_le_add hab.2.1 hcd.2.2
  convert v.map_le_add hleft hright using 1 <;> congr 1 <;> ring

theorem pow {a b:F} (hab:IntegralClose v k a b) (n:ℕ) : IntegralClose v k (a^n) (b^n) := by
  induction n with
  | zero => simpa using one v k
  | succ n ih => simpa only [pow_succ] using mul v k ih hab

end IntegralClose

/-- Congruence preservation for the exact literal Lucas quartic. -/
theorem lucas_congruent (v:AddValuation F (WithTop ℤ)) (k:WithTop ℤ)
    (a b c A B C:F) (ha:IntegralClose v k a A) (hb:IntegralClose v k b B)
    (hc:IntegralClose v k c C) : IntegralClose v k (lucas a b c) (lucas A B C) := by
  have h1:=IntegralClose.one v k
  have h2:IntegralClose v k (2:F) 2 := by convert IntegralClose.add v k h1 h1 using 1 <;> norm_num
  have ht:=IntegralClose.sub v k ha h2
  exact IntegralClose.sub v k (IntegralClose.add v k
    (IntegralClose.sub v k (IntegralClose.pow v k hb 2)
      (IntegralClose.mul v k (IntegralClose.mul v k (IntegralClose.mul v k ha ht) hb) hc))
    (IntegralClose.mul v k (IntegralClose.pow v k ht 2) (IntegralClose.pow v k hc 2))) h1

theorem lucas_transfer (v:AddValuation F (WithTop ℤ)) (k:WithTop ℤ)
    (a b c A B C:F) (ha:IntegralClose v k a A) (hb:IntegralClose v k b B)
    (hc:IntegralClose v k c C) (hsource:k≤v (lucas a b c)) : k≤v (lucas A B C) := by
  have hd: k≤v (lucas a b c-lucas A B C):=(lucas_congruent v k a b c A B C ha hb hc).2.2
  simpa only [sub_sub_cancel] using v.map_le_sub hsource hd

end Algebra

variable (p:ℕ) [Fact p.Prime]

theorem int_integral (n:ℤ) : (0:WithTop ℤ)≤Padic.addValuation (n:ℚ_[p]) := by
  apply (HTail318.norm_le_iff_valuation p (n:ℚ_[p]) 0).mp
  simpa using Padic.norm_int_le_one n

theorem integer_depth_dvd (n:ℤ) (k:ℕ)
    (h:((k:ℤ):WithTop ℤ)≤Padic.addValuation (n:ℚ_[p])) : (p:ℤ)^k∣n := by
  apply TorsionSafeIndex318.padic_norm_bound_dvd p n k
  have hh:‖(n:ℚ_[p])‖≤(p:ℝ)^(-(k:ℤ)) :=
    (HTail318.norm_le_iff_valuation p (n:ℚ_[p]) (k:ℤ)).mpr h
  have hpow:‖(p:ℚ_[p])‖^k=(p:ℝ)^(-(k:ℤ)) := by simp [Padic.norm_p,zpow_neg]
  rwa [hpow]

/-- Exact integer divisibility for the source's high Lucas target. -/
theorem integer_lucas_dvd (a b c:ℚ_[p]) (A B C:ℤ)
    (ha:0≤Padic.addValuation a) (hb:0≤Padic.addValuation b) (hc:0≤Padic.addValuation c)
    (hA:(13:WithTop ℤ)≤Padic.addValuation (a-(A:ℚ_[p])))
    (hB:(13:WithTop ℤ)≤Padic.addValuation (b-(B:ℚ_[p])))
    (hC:(13:WithTop ℤ)≤Padic.addValuation (c-(C:ℚ_[p])))
    (hsource:(13:WithTop ℤ)≤Padic.addValuation (lucas a b c)) :
    (p:ℤ)^13∣B^2-A*(A-2)*B*C+(A-2)^2*C^2-1 := by
  apply integer_depth_dvd p _ 13
  have ht:=lucas_transfer Padic.addValuation (13:WithTop ℤ) a b c (A:ℚ_[p]) (B:ℚ_[p]) (C:ℚ_[p])
    ⟨ha,int_integral p A,hA⟩ ⟨hb,int_integral p B,hB⟩ ⟨hc,int_integral p C,hC⟩ hsource
  norm_num only [lucas,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_ofNat,Int.cast_one] at ht ⊢
  exact ht

end LucasCongruence318
#print axioms LucasCongruence318.integer_lucas_dvd
