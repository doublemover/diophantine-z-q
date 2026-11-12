module
public import ActualTwoDescentRealKummerSigns318
public section
noncomputable section
namespace ActualTwoDescentSameExceptionalImages318
open ActualTwoDescentGoodPrimeValuations318 ActualTwoDescentThreeAdicSecondSquare318
open ActualTwoDescentTwoAdicEvenCoordinates318 ActualTwoDescentFiniteConclusion318
open ActualTwoDescentOldCorePreservation318 ActualTwoDescentExtendedVectors318
open ActualTwoDescentSmallPattern318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- Necessary exceptional local-image restrictions on the literal curve.
This is a theorem about ALL actual points, complementary to the constructed
beta-class points in the predecessor. -/
def ExceptionalImage (n : ℕ) : Prop :=
  (∀ P : LocalPoint (p:=2) n,
    Even (P.x-n).valuation ∧ Even (P.x+3*n).valuation) ∧
  (∀ P : LocalPoint (p:=3) n, ∃ v : ℚ_[3], v ≠ 0 ∧ v^2=P.x-n)

theorem actual_exceptional_image (n : ℕ) (hn : (n : ZMod 12)=11) : ExceptionalImage n := by
  have h4 : (n : ZMod 4)=3 := by
    have h := congrArg (ZMod.castHom (by decide : 4 ∣ 12) (ZMod 4)) hn
    simpa using h
  have h3 : (n : ZMod 3)=2 := by
    have h := congrArg (ZMod.castHom (by decide : 3 ∣ 12) (ZMod 3)) hn
    simpa using h
  have hm : n%4=3 := by
    have h := congrArg ZMod.val h4
    simpa only [ZMod.val_natCast] using h
  exact ⟨actual_two_even_coordinates n hm,actual_three_second_square n h3⟩

/-- Both necessary exceptional images use the SAME final support, including
all retained old primes. No independently reselected auxiliary family is
substituted between the two twists. -/
theorem actual_same_exceptional_images (d : ℕ) {J : Type*} [Fintype J] [DecidableEq J]
    (p : Option (CoreIndex d ⊕ J) → ℕ) (N : ℕ)
    (C : Conclusion p (extend (selector d)) (extend (beta d)) N)
    (C0 : Conclusion (restricted p) (selector d) (beta d) N) :
    ExceptionalImage (∏ i, p i) ∧ ExceptionalImage (∏ i, restricted p i) :=
  ⟨actual_exceptional_image _ C.residue,actual_exceptional_image _ C0.residue⟩

end ActualTwoDescentSameExceptionalImages318
