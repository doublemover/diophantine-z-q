module
public import ActualOriginalFiniteCircleIdentity318
public section
noncomputable section
namespace ActualOriginalCongruenceCircle318
open QuadricCRTAssembly318 ActualOriginalFiniteCircleIdentity318
open scoped BigOperators
set_option maxHeartbeats 16000000

/-- Literal coordinatewise reduction of the ORIGINAL five integers. -/
@[expose] def originalResidue (m : ℕ) (x : Coordinates ℤ) : Coordinates (ZMod m) :=
  mapCoordinates (Int.castRingHom (ZMod m)) x

/-- A congruence class inside an arbitrary finite original integer region.
No CRT enlargement or independent coordinate choice is substituted. -/
@[expose] def originalResidueSlice (m : ℕ) (a : Coordinates (ZMod m))
    (s : Finset (Coordinates ℤ)) : Finset (Coordinates ℤ) :=
  s.filter (fun x => originalResidue m x = a)

theorem actual_original_congruence_circle (κ : ℤ) (m : ℕ)
    (a : Coordinates (ZMod m)) (s : Finset (Coordinates ℤ))
    (w : Coordinates ℤ → ℂ) :
    (∫ θ : ℝ in 0..1, originalCircleSum κ (originalResidueSlice m a s) w
      (θ : AddCircle (1 : ℝ))) =
      ∑ x ∈ s, if originalResidue m x = a ∧ equation κ x = 0 then w x else 0 := by
  rw [actual_original_circle_interval]
  unfold originalWeightedZeros originalResidueSlice
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hr : originalResidue m x = a <;>
    by_cases hq : equation κ x = 0 <;> simp [hr,hq]

/-- Exact congruence compatibility is inherited from the same integer
equation, before any local-density or Euler-product assertion. -/
theorem actual_original_residue_equation (κ : ℤ) (m : ℕ) (x : Coordinates ℤ) :
    equation (κ : ZMod m) (originalResidue m x) = (equation κ x : ZMod m) := by
  exact equation_map (Int.castRingHom (ZMod m)) κ x

end ActualOriginalCongruenceCircle318
