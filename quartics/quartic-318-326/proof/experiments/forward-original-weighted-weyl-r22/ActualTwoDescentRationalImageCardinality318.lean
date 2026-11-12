module
public import ActualTwoDescentOriginalAllPlacesCardinality318
public section
noncomputable section
namespace ActualTwoDescentRationalImageCardinality318
set_option maxHeartbeats 16000000

open ActualTwoDescentConcreteLocalObstruction318 ActualTwoDescentEllipticDoubleQuotient318
open ActualTwoDescentAllPlacesIntersection318

/-- The rational-image subgroup inside the all-place group is EXACTLY the actual E(Q)/2E(Q). -/
def actualRationalImageEquiv (n : ℚ) (hn : n ≠ 0) : DoubleQuotient n ≃ rationalImageInside n hn :=
  Equiv.ofBijective (fun q => ⟨ellipticAllPlacesInjection n hn q,by
    rw [←actual_all_places_injection_range]
    exact ⟨q,rfl⟩⟩)
    ⟨fun x y h => actual_all_places_injection_injective n hn (congrArg Subtype.val h),by
      rintro ⟨z,hz⟩
      rw [←actual_all_places_injection_range] at hz
      obtain ⟨q,hq⟩ := hz
      exact ⟨q,Subtype.ext hq⟩⟩

/-- Exact finite-index identity for the genuine concrete local-to-global obstruction. -/
theorem actual_rational_obstruction_product (n : ℚ) (hn : n ≠ 0) :
    Nat.card (DoubleQuotient n)*Nat.card (LocalObstruction n hn)=Nat.card (allPlacesImage n hn) := by
  rw [Nat.card_congr (actualRationalImageEquiv n hn)]
  exact (rationalImageInside n hn).card_mul_index

end ActualTwoDescentRationalImageCardinality318
