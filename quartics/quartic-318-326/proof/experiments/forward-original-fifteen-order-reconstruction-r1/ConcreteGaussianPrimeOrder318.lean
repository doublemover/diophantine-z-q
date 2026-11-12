module
public import GaussianFixedRayConcretePrime318
public section
noncomputable section
namespace ConcreteGaussianPrimeOrder318
open SelectedQuotientOrders318 SelectedReductionOrder318 ConcretePadic318
open GaussianFixedRayConcretePrime318
local instance : Fact (Nat.Prime 9649) := ⟨rational_prime⟩
/-- The old actual CM/count producers select one of the two genuine p-adic roots. -/
lemma plus_root : ∃ rho : ℚ_[9649], ∃ hr : rho^2=2, pointCount 9649 rho hr=9764 := by
  obtain ⟨rho,hr⟩ := SelectedRayEmbeddings318.square_root 9649 (by norm_num)
  have hc := CanonicalSelectedCounts318.actual_count 9649 rho hr 57 80 full_ray
    residues.1 residues.2 (CanonicalJacobiNorm318.canonical_from_ray 9649 57 80 full_ray)
  rw [quarter_values.1,quarter_values.2] at hc
  rcases hc with hm|hp
  · have hs := ActualConjugateCounts318.count_sum_from_ray 9649 rho hr 57 80
      full_ray residues.1 residues.2
    refine ⟨-rho,negative_root 9649 rho hr,?_⟩
    omega
  · exact ⟨rho,hr,hp⟩
/-- Actual native quotient order2441; the opposite order is only bounded here. -/
theorem actual_order : ∃ rho : ℚ_[9649], ∃ hr : rho^2=2,
    order 9649 rho hr=2441 ∧
    order 9649 (-rho) (negative_root 9649 rho hr)∣2384 ∧
    1<order 9649 (-rho) (negative_root 9649 rho hr) ∧
    Nat.Coprime (order 9649 rho hr) (order 9649 (-rho) (negative_root 9649 rho hr)) := by
  obtain ⟨rho,hr,hc⟩ := plus_root
  have hs := ActualConjugateCounts318.count_sum_from_ray 9649 rho hr 57 80
    full_ray residues.1 residues.2
  have hc' : pointCount 9649 (-rho) (negative_root 9649 rho hr)=9536 := by omega
  have hp : (9649:ℕ)≠2 := by decide
  have h7 : ¬(9649:ℕ)∣49 := by decide
  have ho := SelectedQuarterOrder318.actual_order_dvd_quarter 9649 rho hr hp h7
    1743 1075 finite_roots.1 finite_roots.2
  rw [hc] at ho
  change order 9649 rho hr∣2441 at ho
  have he := SelectedExactOrderCertificates318.prime_upper 9649 rho hr 2441 (by norm_num) ho
  have hd := SelectedQuarterOrder318.actual_order_dvd_quarter 9649 (-rho)
    (negative_root 9649 rho hr) hp h7 1743 1075 finite_roots.1 finite_roots.2
  rw [hc'] at hd
  change order 9649 (-rho) (negative_root 9649 rho hr)∣2384 at hd
  refine ⟨rho,hr,he,hd,SelectedOriginalGeneratorNonzero318.order_gt_one _ _ _,?_⟩
  rw [he]
  exact Nat.Coprime.of_dvd_right hd (by decide : Nat.Coprime 2441 2384)
end ConcreteGaussianPrimeOrder318
