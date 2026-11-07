module
public import Mathlib.NumberTheory.FundamentalDiscriminant
public import Mathlib.Tactic
public section
noncomputable section
open Finset
namespace CMDiscriminant318
set_option maxHeartbeats 0

@[expose] def radical (n:ℕ) : ℕ := ∏p∈n.primeFactors,p

 theorem squarefree_support_bound (a b:ℕ) (ha:Squarefree a) (hb:b≠0)
    (hsub:∀p:ℕ,p.Prime→p∣a→p∣b) : a≤radical b := by
  rw [←Nat.prod_primeFactors_of_squarefree ha]
  apply prod_le_prod_of_subset_of_one_le
  · intro p hp
    obtain ⟨hprime,hpa,_⟩:=Nat.mem_primeFactors.mp hp
    exact Nat.mem_primeFactors.mpr ⟨hprime,hsub p hprime hpa,hb⟩
  · intro p hp _
    exact (Nat.prime_of_mem_primeFactors hp).one_lt.le

/-- The factor four for a quadratic fundamental discriminant is proved
from Mathlib's actual fundamental-discriminant predicate and actual finite
prime support; it is not supplied as a numerical hypothesis. -/
theorem fundamental_discriminant_bound (D:ℤ) (B:ℕ)
    (hD:Int.IsFundamentalDiscr D) (hB:B≠0)
    (hsupport:∀p:ℕ,p.Prime→p∣D.natAbs→p∣B) : D.natAbs≤4*radical B := by
  rcases Int.isFundamentalDiscr_iff_squarefree.mp hD with ⟨_,hsq⟩|⟨hmod,hsq,_⟩
  · have hs:=squarefree_support_bound D.natAbs B (Int.squarefree_natAbs.mpr hsq) hB hsupport
    omega
  · have hd: (4:ℤ)∣D:=Int.dvd_iff_emod_eq_zero.mpr hmod
    have he:D=4*(D/4):=(Int.mul_ediv_cancel' hd).symm
    have habs:D.natAbs=4*(D/4).natAbs := by
      nth_rw 1 [he]
      rw [Int.natAbs_mul]
      norm_num
    have hs:(D/4).natAbs≤radical B:=squarefree_support_bound _ B
      (Int.squarefree_natAbs.mpr hsq) hB (by
        intro p hp hpd
        apply hsupport p hp
        rw [habs]
        exact hpd.trans (dvd_mul_left _ _))
    rw [habs]
    omega

 theorem real_discriminant_bound (D:ℤ) (B:ℕ) (R:ℝ)
    (hD:Int.IsFundamentalDiscr D) (hB:B≠0)
    (hsupport:∀p:ℕ,p.Prime→p∣D.natAbs→p∣B)
    (hR:(radical B:ℝ)≤R) : (D.natAbs:ℝ)≤4*R := by
  have hd:(D.natAbs:ℝ)≤4*(radical B:ℝ):=by exact_mod_cast fundamental_discriminant_bound D B hD hB hsupport
  linarith

end CMDiscriminant318
#print axioms CMDiscriminant318.fundamental_discriminant_bound
