module
public import CanonicalCMNormBridge318
public section
noncomputable section
namespace CanonicalCurveParity318
open GoodReductionResidue318 GoodReductionLifting318 GoodReductionCardinality318
open ReciprocalDouble318 WeierstrassCurve.Affine FiniteCurveCharacterCount318
set_option maxHeartbeats 1000000
variable (p : ℕ) [Fact p.Prime]

/-- Four literal two-torsion classes on the square-unit coefficient1
force divisibility of the actual canonical finite-curve count. -/
theorem four_dvd_count (hp : p≠2) : 4∣count (1:ZMod p) := by
  classical
  let a : ℤ_[p] := 1
  have ha : ‖a‖=1 := by simp [a]
  let q := QuotientAddGroup.mk' (GoodReductionLifting318.subgroup p (a^2))
  let A := q (point p (a^2) (ActualFourTorsion318.square_unit p a ha)
    (ActualFourTorsion318.zeroRoot p a))
  let B := q (point p (a^2) (ActualFourTorsion318.square_unit p a ha)
    (ActualFourTorsion318.positiveRoot p a))
  letI : Finite ((E ((a^2:ℤ_[p]):ℚ_[p])).Point ⧸ GoodReductionLifting318.subgroup p (a^2)) :=
    Finite.of_equiv (Option (ResidueCurve p (a^2)))
      (equivalence p hp (a^2) (ActualFourTorsion318.square_unit p a ha))
  obtain ⟨hAA,hBB,hA,hB,hAB⟩ := ActualFourTorsion318.distinct_torsion p a ha
  let H := FourTorsionQuotient318.subgroup A B hAA hBB
  have hH : Nat.card H=4 := FourTorsionQuotient318.subgroup_card A B hAA hBB hA hB hAB
  have he := H.card_mul_index
  rw [hH,cardinality p hp (a^2) (ActualFourTorsion318.square_unit p a ha)] at he
  refine ⟨H.index,?_⟩
  simpa [a,FiniteCurveCharacterCount318.count,FiniteCurveCharacterCount318.Curve,
    GoodReductionResidue318.ResidueCurve] using he.symm

/-- Odd real Frobenius coordinate follows from the ACTUAL canonical
curve and p≡1 mod4, not a Gaussian associate-selection assumption. -/
theorem odd_half_trace (hp4 : p%4=1) (c : ℤ)
    (htrace : traceSum (1:ZMod p)=2*c) : c%2=1 := by
  have hp2 : p≠2 := by omega
  obtain ⟨k,hk⟩ := four_dvd_count p hp2
  have hkz : (count (1:ZMod p):ℤ)=4*(k:ℤ) := by exact_mod_cast hk
  have hf := count_formula (by simpa only [ringChar_zmod_n] using hp2 : ringChar (ZMod p)≠2)
    (1:ZMod p)
  simp only [ZMod.card,htrace] at hf
  have hm : (p:ℤ)%4=1 := by exact_mod_cast hp4
  omega

end CanonicalCurveParity318
