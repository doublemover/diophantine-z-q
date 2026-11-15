module
public import ActualTwoDescentRealPairConstruction318
public section
noncomputable section
namespace ActualTwoDescentAdelicBadPlaceImages318
set_option maxHeartbeats 16000000

open ActualTwoDescentAdelicPairData318 ActualTwoDescentRealPairConstruction318
open ActualTwoDescentSignedLocalTranslation318 ActualTwoDescentSignedAllBadNormalization318
open ActualTwoDescentSignedRealNormalization318 ActualTwoDescentCoordinateSymbols318
open ActualTwoDescentSignedRepresentativeTransport318
open scoped BigOperators
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- Normalized rational representatives inherit genuine local witnesses from the adelic pair. -/
theorem actual_adelic_all_bad_images (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (A B : ℚ) (H : AdelicPair (∏ i, p i) A B) (ε δ : ZMod 2) (u v : Option U → ZMod 2)
    (r s : ℚ) (hr : r ≠ 0) (hs : s ≠ 0)
    (hA : A=(firstRepresentative p δ u : ℚ)*r^2)
    (hB : B=(signedSecond p ε v : ℚ)*s^2) : SignedAllBadRepresented p ε δ u v := by
  have hloc (q : ℕ) [Fact q.Prime] : SignedRepresentedAt q p ε δ u v := by
    obtain ⟨P,a,b,ha,hb,hPa,hPb⟩ := H.finite_places q
    have hAc : (A : ℚ_[q])=(firstRepresentative p δ u : ℚ_[q])*(r : ℚ_[q])^2 := by exact_mod_cast hA
    have hBc : (B : ℚ_[q])=(signedSecond p ε v : ℚ_[q])*(s : ℚ_[q])^2 := by exact_mod_cast hB
    refine ⟨P,(r : ℚ_[q])*a,(s : ℚ_[q])*b,
      mul_ne_zero (Rat.cast_ne_zero.mpr hr) ha,mul_ne_zero (Rat.cast_ne_zero.mpr hs) hb,?_,?_⟩
    · rw [hPa,hAc]; ring
    · rw [hPb,hBc]; ring
  refine ⟨fun i => hloc (p i),hloc 3,hloc 2,?_⟩
  have hn : 0 < ((∏ i, p i : ℕ) : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
  obtain ⟨x,y,hx,hminus,hplus,hcurve,a,b,ha,hb,hPa,hPb⟩ :=
    actual_real_pair_representative ((∏ i, p i : ℕ) : ℝ) (A : ℝ) (B : ℝ) hn
      (by exact_mod_cast H.first_pos) (Rat.cast_ne_zero.mpr H.second_ne)
  have hAc : (A : ℝ)=(firstRepresentative p δ u : ℝ)*(r : ℝ)^2 := by exact_mod_cast hA
  have hBc : (B : ℝ)=(signedSecond p ε v : ℝ)*(s : ℝ)^2 := by exact_mod_cast hB
  refine ⟨x,y,hx,hminus,hplus,hcurve,(r : ℝ)*a,(s : ℝ)*b,
    mul_ne_zero (Rat.cast_ne_zero.mpr hr) ha,mul_ne_zero (Rat.cast_ne_zero.mpr hs) hb,?_,?_⟩
  · rw [hPa,hAc]; ring
  · rw [hPb,hBc]; ring

end ActualTwoDescentAdelicBadPlaceImages318
