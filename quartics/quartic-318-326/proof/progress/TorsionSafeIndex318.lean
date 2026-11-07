module
public import SourcePole318
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public section
namespace TorsionSafeIndex318
set_option maxHeartbeats 0
variable {G F:Type*} [AddCommGroup G] [Field F] [CharZero F]

/-- Kill the common rational two-torsion before applying a local logarithm.
The global generator itself need not belong to the local subgroup. -/
theorem double_relation (P H R tau:G) (n c:ℤ)
    (hH:H=n • P+tau) (hR:R=c • P) (htau:(2:ℤ) • tau=0) :
    (2*n) • R=(2*c) • H := by
  have ht:(2*c) • tau=0 := by rw [mul_comm, mul_zsmul, htau, smul_zero]
  rw [hH,hR,zsmul_add,ht,add_zero]
  simp only [←mul_zsmul]
  congr 1
  ring

/-- Exact torsion-safe scalar identity for any actual subgroup homomorphism. -/
theorem logarithm_relation (S:AddSubgroup G) (ell:S→+F)
    (P H R tau:G) (n c:ℤ) (hHS:H∈S) (hRS:R∈S)
    (hH:H=n • P+tau) (hR:R=c • P) (htau:(2:ℤ) • tau=0) :
    (n:F)*ell ⟨R,hRS⟩=(c:F)*ell ⟨H,hHS⟩ := by
  have he:(2*n) • (⟨R,hRS⟩:S)=(2*c) • (⟨H,hHS⟩:S) := by
    apply Subtype.ext
    exact double_relation P H R tau n c hH hR htau
  have hl:=congrArg ell he
  simp only [map_zsmul, zsmul_eq_mul,Int.cast_mul,Int.cast_ofNat] at hl
  linear_combination hl / 2

/-- Finite local logarithm values determine the integer valuation gain.
Only the honest rational restriction of the normalized valuation is used. -/
theorem valuation_gain (p:ℕ) [Fact p.Prime]
    (v:AddValuation F (WithTop ℤ))
    (vint:∀z:ℤ,z≠0 → v (z:F)=(padicValInt p z:ℤ))
    (LH LR:F) (h r:ℤ) (hLH:v LH=h) (hLR:v LR=r)
    (n c:ℤ) (hc:c≠0) (he:(n:F)*LR=(c:F)*LH) :
    (padicValInt p c:ℤ)=(padicValInt p n:ℤ)+r-h := by
  have hL0:LH≠0 := (v.ne_top_iff).mp (by rw [hLH]; simp)
  have hn:n≠0 := by
    intro hn
    rw [hn,Int.cast_zero,zero_mul] at he
    exact mul_ne_zero (Int.cast_ne_zero.mpr hc) hL0 he.symm
  have hv:=congrArg v he
  rw [v.map_mul,v.map_mul,vint n hn,vint c hc,hLH,hLR] at hv
  have hv':(padicValInt p n:ℤ)+r=(padicValInt p c:ℤ)+h := by exact_mod_cast hv
  omega

/-- A gain of k in logarithm depth forces p^k to divide the signed scalar
index. The zero scalar branch is included, not silently inverted. -/
theorem index_divisibility (p:ℕ) [Fact p.Prime]
    (v:AddValuation F (WithTop ℤ))
    (vint:∀z:ℤ,z≠0 → v (z:F)=(padicValInt p z:ℤ))
    (LH LR:F) (h r:ℤ) (hLH:v LH=h) (hLR:v LR=r)
    (n c:ℤ) (k:ℕ) (he:(n:F)*LR=(c:F)*LH) (hgain:(k:ℤ)≤r-h) :
    (p:ℤ)^k∣c := by
  by_cases hc:c=0
  · rw [hc]; exact dvd_zero _
  have hv:=valuation_gain p v vint LH LR h r hLH hLR n c hc he
  have hle:k≤padicValInt p c := by omega
  rw [←Nat.cast_pow,Int.natCast_dvd]
  exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hc)).mpr hle

/-- Fully assembled group/log/valuation implication. In an application the
homomorphism is the constructed actual local elliptic logarithm. -/
theorem torsion_safe_divisibility (S:AddSubgroup G) (ell:S→+F)
    (p:ℕ) [Fact p.Prime] (v:AddValuation F (WithTop ℤ))
    (vint:∀z:ℤ,z≠0 → v (z:F)=(padicValInt p z:ℤ))
    (P H R tau:G) (n c:ℤ) (hHS:H∈S) (hRS:R∈S)
    (hH:H=n • P+tau) (hR:R=c • P) (htau:(2:ℤ) • tau=0)
    (h r:ℤ) (hLH:v (ell ⟨H,hHS⟩)=h) (hLR:v (ell ⟨R,hRS⟩)=r)
    (k:ℕ) (hgain:(k:ℤ)≤r-h) : (p:ℤ)^k∣c :=
  index_divisibility p v vint _ _ h r hLH hLR n c k
    (logarithm_relation S ell P H R tau n c hHS hRS hH hR htau) hgain

/-- The actual p-adic norm bound on an integer is precisely a prime-power
 divisibility bound, with the zero integer handled separately. -/
theorem padic_norm_bound_dvd (p:ℕ) [Fact p.Prime] (c:ℤ) (k:ℕ)
    (hbound:‖(c:ℚ_[p])‖≤‖(p:ℚ_[p])‖^k) : (p:ℤ)^k∣c := by
  by_cases hc:c=0
  · rw [hc]; exact dvd_zero _
  have hpow:‖(p:ℚ_[p])‖^k=(p:ℝ)^(-(k:ℤ)) := by
    simp [Padic.norm_p,zpow_neg]
  rw [Padic.norm_eq_zpow_neg_valuation (Int.cast_ne_zero.mpr hc),
    Padic.valuation_intCast,hpow] at hbound
  have hp:1<(p:ℝ) := by exact_mod_cast (Fact.out:p.Prime).one_lt
  have hle:k≤padicValInt p c := by
    have hh:-(padicValInt p c:ℤ)≤-(k:ℤ) := (zpow_le_zpow_iff_right₀ hp).mp hbound
    omega
  rw [←Nat.cast_pow,Int.natCast_dvd]
  exact (padicValNat_dvd_iff_le (Int.natAbs_ne_zero.mpr hc)).mpr hle

section Normed
variable {L:Type*} [NormedField L] [CharZero L]

/-- Norm-only version for any actual complete-field realization. It avoids
 assuming an integer-valued valuation already defined on its completion. -/
theorem norm_index_divisibility (p:ℕ) [Fact p.Prime]
    (intNorm:∀z:ℤ,‖(z:L)‖=‖(z:ℚ_[p])‖)
    (LH LR:L) (hLH:LH≠0) (n c:ℤ) (k:ℕ)
    (he:(n:L)*LR=(c:L)*LH) (hgain:‖LR‖≤‖(p:ℚ_[p])‖^k*‖LH‖) :
    (p:ℤ)^k∣c := by
  have hn:‖(n:L)‖≤1 := by rw [intNorm]; exact Padic.norm_int_le_one n
  have hcomp:‖(c:L)‖*‖LH‖≤‖(p:ℚ_[p])‖^k*‖LH‖ := by
    calc
      _=‖(n:L)‖*‖LR‖ := by simpa only [norm_mul] using (congrArg norm he).symm
      _≤‖LR‖ := mul_le_of_le_one_left (norm_nonneg _) hn
      _≤_ := hgain
  have hb:‖(c:L)‖≤‖(p:ℚ_[p])‖^k :=
    (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hLH)).mp hcomp
  rw [intNorm] at hb
  exact padic_norm_bound_dvd p c k hb

/-- Torsion-safe comparison over either an actual split or inert local
 field, using the norm normalization already proved for that field. -/
theorem torsion_safe_norm_divisibility (S:AddSubgroup G) (ell:S→+L)
    (p:ℕ) [Fact p.Prime] (intNorm:∀z:ℤ,‖(z:L)‖=‖(z:ℚ_[p])‖)
    (P H R tau:G) (n c:ℤ) (hHS:H∈S) (hRS:R∈S)
    (hH:H=n • P+tau) (hR:R=c • P) (htau:(2:ℤ) • tau=0)
    (hLH:ell ⟨H,hHS⟩≠0) (k:ℕ)
    (hgain:‖ell ⟨R,hRS⟩‖≤‖(p:ℚ_[p])‖^k*‖ell ⟨H,hHS⟩‖) :
    (p:ℤ)^k∣c :=
  norm_index_divisibility p intNorm _ _ hLH n c k
    (logarithm_relation S ell P H R tau n c hHS hRS hH hR htau) hgain
end Normed

end TorsionSafeIndex318
#print axioms TorsionSafeIndex318.logarithm_relation
#print axioms TorsionSafeIndex318.torsion_safe_divisibility

#print axioms TorsionSafeIndex318.torsion_safe_norm_divisibility
