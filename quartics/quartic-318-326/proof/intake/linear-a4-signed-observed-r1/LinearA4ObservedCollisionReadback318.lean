module
public import LinearA4CollisionBins318
public import LinearObservationReconstruction318
public section
noncomputable section

namespace LinearA4ObservedCollisionReadback318

open LinearObservationReconstruction318
open LinearA4CollisionBins318

abbrev Coordinates := (ℤ × ℤ) × (ℤ × ℤ)

/-- The same signed coordinate tuple both recovers the original affine key
and lands in the specified collision bins. In the diagonal case, the
second slot is used only for reconstruction: both divisibilities act
on the first signed Gaussian pair. -/
theorem injective_and_mem {α : Type*} {Q : ℤ} (hQ : Q ≠ 0)
    {a b : Slot} (hab : a ≠ b) (p : ℕ) [Fact p.Prime] (diagonal : Bool)
    (rows : α → Key) (hrows : Function.Injective rows) (g : α → Coordinates)
    (leftNorm : ∀ x, (g x).1.1^2 + (g x).1.2^2 = value Q a (rows x))
    (rightNorm : ∀ x, (g x).2.1^2 + (g x).2.2^2 = value Q b (rows x))
    (minusDiv : ∀ x, (p:ℤ) ∣ ((g x).1.1-1)^2 + (g x).1.2^2)
    (plusDiv : ∀ x, let z := (if diagonal then (g x).1 else (g x).2);
      (p:ℤ) ∣ (z.1+1)^2 + z.2^2) :
    Function.Injective g ∧
      ∀ x, (reducePlane p (g x).1, reducePlane p (g x).2) ∈
        (if diagonal then diagonalBins else crossBins) := by
  refine ⟨injective_coordinates hQ hab rows hrows g leftNorm rightNorm, ?_⟩
  intro x
  cases diagonal with
  | false =>
    change (reducePlane p (g x).1, reducePlane p (g x).2) ∈ crossBins
    exact cross_mem_of_dvd p (g x).1 (g x).2 (minusDiv x) (plusDiv x)
  | true =>
    change (reducePlane p (g x).1, reducePlane p (g x).2) ∈ diagonalBins
    exact diagonal_mem_of_dvd p (g x).1 (g x).2 (minusDiv x) (plusDiv x)

end LinearA4ObservedCollisionReadback318
