module
public import ActualTwoDescentActualShaPrimaryClassification318
public section
noncomputable section
namespace ActualTwoDescentActualShaDualityClassification318
set_option maxHeartbeats 16000000

open ActualTwoDescentActualShaPrimary318 ActualTwoDescentActualShaDivisibleBranch318
open ActualTwoDescentActualShaPruefer318 ActualTwoDescentDyadicPrueferModel318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentAllPlacesIntersection318

/-- With the genuine finite-primary alternating pairing still explicitly required, the actual full primary Sha is zero or a single standard Prüfer group. This is the precise corank-side structure, not rational rank selection. -/
theorem actual_sha_zero_or_pruefer_from_finite_pairing
    (n : ℚ) (hn : n ≠ 0) (hf : Finite (DoubleQuotient n)) (hb : Nat.card (DoubleQuotient n) ≤ 8)
    (hS : Nat.card (allPlacesImage n hn)=8) {A : Type*} [CommGroup A]
    (hpair : Finite (actualShaPrimary n hn) → ∃ e : actualShaPrimary n hn →* (actualShaPrimary n hn →* A),
      (∀ x, e x x=1) ∧ (∀ x, (∀ y, e x y=1) → x=1)) :
    Subsingleton (actualShaPrimary n hn) ∨ Nonempty (actualShaPrimary n hn ≃* PrueferTwo) := by
  rcases actual_sha_primary_zero_or_divisible_from_finite_pairing n hn hf hb hS hpair with hzero|⟨hinf,_⟩
  · exact Or.inl hzero
  · letI := hinf
    exact Or.inr (actual_infinite_sha_pruefer n hn hf hb hS)

end ActualTwoDescentActualShaDualityClassification318
