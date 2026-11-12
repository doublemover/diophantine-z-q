module
public import ActualSelbergLogDenominator318
public section
noncomputable section
namespace FiniteWeightedResidueDiscrepancy318
open scoped BigOperators
set_option maxHeartbeats 16000000
variable {X R : Type*} [DecidableEq X] [Fintype R] [DecidableEq R]

/-- The actual weighted fiber, keeping multiplicities of distinct original
points that share a residue. -/
@[expose] def fiber (S : Finset X) (w : X → ℝ) (ρ : X → R) (r : R) : ℝ :=
  ∑ x∈S.filter (fun x => ρ x=r),w x

lemma fiber_sum (S : Finset X) (w : X → ℝ) (ρ : X → R) :
    ∑ r : R,fiber S w ρ r=∑ x∈S,w x := by
  exact Finset.sum_fiberwise_of_maps_to (fun _ _ => Finset.mem_univ _) _

/-- The same actual points, not their image, comprise the prescribed
residue event. -/
lemma event_sum (S : Finset X) (w : X → ℝ) (ρ : X → R) (A : Finset R) :
    (∑ x∈S,if ρ x∈A then w x else 0)=∑ r∈A,fiber S w ρ r := by
  have hh := Finset.sum_fiberwise_of_maps_to
    (fun x (hx : x∈S.filter (fun x => ρ x∈A)) => (Finset.mem_filter.mp hx).2) w
  have he : (∑ x∈S.filter (fun x => ρ x∈A),w x)=
      ∑ x∈S,if ρ x∈A then w x else 0 := by rw [Finset.sum_filter]
  rw [he] at hh
  rw [←hh]
  apply Finset.sum_congr rfl
  intro r hr
  unfold fiber
  apply Finset.sum_congr
  · ext x
    simp only [Finset.mem_filter,and_assoc]
    constructor
    · rintro ⟨hx,hA,he⟩
      exact ⟨hx,he⟩
    · rintro ⟨hx,he⟩
      exact ⟨hx,by simpa only [he] using hr,he⟩
  · intro _ _
    rfl

/-- Exact centered discrepancy for an ACTUAL residue set. The common
mass M is arbitrary here, so the identity also serves the true analytic
main term once that term has been produced. -/
theorem event_discrepancy (S : Finset X) (w : X → ℝ) (ρ : X → R)
    (A : Finset R) (M : ℝ) :
    (∑ x∈S,if ρ x∈A then w x else 0)-(A.card:ℝ)*M=
      ∑ r∈A,(fiber S w ρ r-M) := by
  rw [event_sum,Finset.sum_sub_distrib,Finset.sum_const,nsmul_eq_mul]

/-- The resulting bound uses the actual weighted fiber errors. It does
not assert that finite CRT makes integer fibers equidistributed. -/
theorem actual_discrepancy_bound (S : Finset X) (w : X → ℝ) (ρ : X → R)
    (A : Finset R) (M : ℝ) :
    |(∑ x∈S,if ρ x∈A then w x else 0)-(A.card:ℝ)*M|≤
      ∑ r∈A,|fiber S w ρ r-M| := by
  rw [event_discrepancy]
  exact Finset.abs_sum_le_sum_abs _ _

end FiniteWeightedResidueDiscrepancy318
