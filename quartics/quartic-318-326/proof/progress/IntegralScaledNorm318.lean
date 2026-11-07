module
public import IntegralScaledBounds318
public section
namespace IntegralScaledNorm318
open IntegralRingEvaluation318 IntegralScaledSeries318 IntegralScaledBounds318
variable (p : ℕ) [Fact p.Prime] (hp : 19 ≤ p)
variable {R : Type*} [NormedCommRing R] [CompleteSpace R] [IsUltrametricDist R] [NormBoundOne R]
variable (ι : ℤ_[p] →+* R) (D : R) (hι : Isometry ι)
set_option linter.unusedSectionVars false

include hι in
theorem norm_of_isUnit (x : R) (hx : IsUnit x) : ‖x‖=1 := by
  have hone : ‖(1 : R)‖=1 := by simpa only [map_one, norm_one] using inclusion_norm p ι hι 1
  obtain ⟨u,rfl⟩ := hx
  apply le_antisymm (NormBoundOne.norm_le_one _)
  calc
    1 = ‖(u : R)*(↑u⁻¹ : R)‖ := by rw [Units.mul_inv, hone]
    _ ≤ ‖(u : R)‖*‖(↑u⁻¹ : R)‖ := norm_mul_le _ _
    _ ≤ ‖(u : R)‖ := mul_le_of_le_one_right (norm_nonneg _) (NormBoundOne.norm_le_one _)

include hι in
theorem H_norm (t : R) : ‖eval R (H p hp ι D) t‖=1 :=
  norm_of_isUnit p ι hι _ (H_isUnit p hp ι D hι t)

include hι in
theorem B_norm (t : R) : ‖eval R (B p hp ι D) t‖=1 :=
  norm_of_isUnit p ι hι _ (B_isUnit p hp ι D hι t)

include hι in
theorem branch_norm (t : R) : ‖eval R (branch p hp ι D) t‖=1 :=
  norm_of_isUnit p ι hι _ (branch_isUnit p hp ι D hι t)

theorem norm_map {K : Type*} [NormedRing K] (φ : R →+* K) (hφ : Isometry φ) (x : R) :
    ‖φ x‖=‖x‖ := by
  simpa only [map_zero, dist_zero_right] using hφ.dist_eq x 0

include hι in
theorem H_map_norm {K : Type*} [NormedRing K] (φ : R →+* K) (hφ : Isometry φ) (t : R) :
    ‖φ (eval R (H p hp ι D) t)‖=1 := by
  rw [norm_map φ hφ, H_norm p hp ι D hι]

include hι in
theorem B_map_norm {K : Type*} [NormedRing K] (φ : R →+* K) (hφ : Isometry φ) (t : R) :
    ‖φ (eval R (B p hp ι D) t)‖=1 := by
  rw [norm_map φ hφ, B_norm p hp ι D hι]

include hι in
theorem branch_map_norm {K : Type*} [NormedRing K] (φ : R →+* K) (hφ : Isometry φ) (t : R) :
    ‖φ (eval R (branch p hp ι D) t)‖=1 := by
  rw [norm_map φ hφ, branch_norm p hp ι D hι]

end IntegralScaledNorm318
#print axioms IntegralScaledNorm318.H_norm
#print axioms IntegralScaledNorm318.branch_map_norm
