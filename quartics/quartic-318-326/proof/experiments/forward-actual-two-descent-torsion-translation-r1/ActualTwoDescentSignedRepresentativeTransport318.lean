module
public import ActualTwoDescentTranslatedLocalPoint318
public section
noncomputable section
namespace ActualTwoDescentSignedRepresentativeTransport318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentCoordinateSymbols318
open ActualTwoDescentComplementMonomial318 ActualTwoDescentZeroSumCompletion318
open ActualTwoDescentSignedComparisons318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {U : Type*} [Fintype U] [DecidableEq U]

def signedSecond (p : Option U → ℕ) (ε : ZMod 2) (v : Option U → ZMod 2) : ℤ :=
  (-1)^ε.val*(monomial p v : ℤ)

lemma actual_first_torsion_transport {K : Type*} [Field K] [CharZero K]
    (p : Option U → ℕ) (δ : ZMod 2) (u : Option U → ZMod 2) :
    3*(firstRepresentative p δ u : K)=
      (firstRepresentative p (δ+1) u : K)*((3 : K)^δ.val)^2 := by
  fin_cases δ <;> simp [firstRepresentative] <;> ring

lemma actual_second_torsion_transport {K : Type*} [Field K] [CharZero K]
    (p : Option U → ℕ) (ε : ZMod 2) (v : Option U → ZMod 2) :
    (-((∏ i, p i : ℕ) : K))*(signedSecond p ε v : K)=
      (signedSecond p (ε+1) (toggle 1 v) : K)*(monomial p v : K)^2 := by
  have he : (monomial p (toggle 1 v) : K)*(monomial p v : K)=(∏ i, p i : ℕ) := by
    have h := actual_complement_product p v
    simp only [toggle,one_smul,add_comm v] at *
    exact_mod_cast h
  rw [←he]
  fin_cases ε <;> simp [signedSecond] <;> ring

end ActualTwoDescentSignedRepresentativeTransport318
