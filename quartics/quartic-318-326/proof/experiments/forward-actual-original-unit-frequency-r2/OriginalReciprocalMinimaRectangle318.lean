module
public import OriginalDeterminantMinima318
public section
noncomputable section
namespace OriginalReciprocalMinimaRectangle318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalControlledIntegralBasis318 OriginalCofactorCoordinates318
open OriginalAnisotropicRectangle318 OriginalThirdMinimumTail318 OriginalDeterminantMinima318
set_option maxHeartbeats 4000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma ratio_control (A B C Z D R k : ℝ) (hA : 0<A) (hB : 0≤B)
    (hD : 0<D) (hR : 0≤R) (hk : 0≤k) (hZ : Z≤k*C)
    (hdet : A*B*C≤4*D) : R*(B*Z)/D≤(4*k*R)/A := by
  apply (div_le_div_iff₀ hD hA).mpr
  calc
    R*(B*Z)*A≤R*(B*(k*C))*A := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hZ hB) hR) hA.le
    _ = (k*R)*(A*B*C) := by ring
    _ ≤ (k*R)*(4*D) := mul_le_mul_of_nonneg_left hdet (mul_nonneg hk hR)
    _ = 4*k*R*D := by ring

lemma floorRadius_mono {A B : ℝ} (h : A≤B) : floorRadius A≤floorRadius B :=
  Int.toNat_le_toNat (Int.floor_mono h)

/-- Actual reduced-whole-basis inverse radii are at most 8R/λ1,
8R/λ2,4R/λ3. The determinant lower bound is CONSTRUCTED by nearest-plane
rounding and actual minimality; it is not a geometric-sieve hypothesis. -/
theorem reciprocal_radii (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) (u v w z : Vector ℤ)
    (hb : IntegralBasisTriple p κ t u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2) (hz : ‖embed z‖≤2*‖embed w‖)
    (hwmin : ∀ y : Vector ℤ, y∈literalLattice p κ t →
      embed y∉Submodule.span ℝ (Set.range ![embed u,embed v]) → ‖embed w‖≤‖embed y‖)
    (R : ℝ) (hR : 0≤R) :
    inverseRadius v z (determinant u v z) R≤floorRadius (8*R/‖embed u‖) ∧
    inverseRadius z u (determinant u v z) R≤floorRadius (8*R/‖embed v‖) ∧
    inverseRadius u v (determinant u v z) R≤floorRadius (4*R/‖embed w‖) := by
  have hU : 0<‖embed u‖ := norm_pos_iff.mpr (hb.1.2.ne_zero 0)
  have hV : 0<‖embed v‖ := hU.trans_le huv
  have hW : 0<‖embed w‖ := hV.trans_le hvw
  have hD : 0<|(determinant u v z:ℝ)| := by
    apply abs_pos.mpr
    exact_mod_cast determinant_ne_zero p hp κ t u v z hb huv hip
  have hdet := actual_determinant_lower p hp κ t u v w z hb huv hvw hip hwmin
  have hfirst := ratio_control ‖embed u‖ ‖embed v‖ ‖embed w‖ ‖embed z‖
    |(determinant u v z:ℝ)| R 2 hU (norm_nonneg _) hD hR (by norm_num) hz hdet
  have hsecond := ratio_control ‖embed v‖ ‖embed u‖ ‖embed w‖ ‖embed z‖
    |(determinant u v z:ℝ)| R 2 hV (norm_nonneg _) hD hR (by norm_num) hz
    (by simpa only [mul_comm ‖embed v‖ ‖embed u‖] using hdet)
  have hthird := ratio_control ‖embed w‖ ‖embed u‖ ‖embed v‖ ‖embed v‖
    |(determinant u v z:ℝ)| R 1 hW (norm_nonneg _) hD hR (by norm_num) (by simp)
    (by nlinarith only [hdet])
  refine ⟨floorRadius_mono ?_,floorRadius_mono ?_,floorRadius_mono ?_⟩
  · simpa only [show (4:ℝ)*2=8 by norm_num] using hfirst
  · simpa only [mul_comm ‖embed u‖ ‖embed z‖,show (4:ℝ)*2=8 by norm_num] using hsecond
  · simpa only [mul_one] using hthird

/-- No basis/minimum input remains: the actual original lattice has a
constructed reciprocal-minimum rectangle and its exact finite point bound.
This is the controlled-basis geometry needed by the GOOD-lattice sieve,
not a claim that the remaining polynomial sieve error is already bounded. -/
theorem actual_reciprocal_minima_rectangle (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (κ : ℤ) (t : ∀ i, Option (ZMod (p i))) :
    ∃ u v w z : Vector ℤ, IntegralBasisTriple p κ t u v z ∧
      0<‖embed u‖ ∧ ‖embed u‖≤‖embed v‖ ∧ ‖embed v‖≤‖embed w‖ ∧
      ‖embed z‖≤2*‖embed w‖ ∧
      (∀ y, y∈literalLattice p κ t → embed y≠0 → ‖embed u‖≤‖embed y‖) ∧
      (∀ y, y∈literalLattice p κ t → embed y∉OriginalSaturatedPlane318.line u → ‖embed v‖≤‖embed y‖) ∧
      (∀ y, y∈literalLattice p κ t →
        embed y∉Submodule.span ℝ (Set.range ![embed u,embed v]) → ‖embed w‖≤‖embed y‖) ∧
      ∀ R : ℝ, 0≤R → Nat.card (NormPoints p κ t R)≤
        (2*floorRadius (8*R/‖embed u‖)+1)*
        (2*floorRadius (8*R/‖embed v‖)+1)*
        (2*floorRadius (4*R/‖embed w‖)+1) := by
  obtain ⟨u,v,w,z,hi,hb,huv,hvw,hip,hz,humin,hvmin,hwmin⟩ := actual_controlled_basis p hp κ t
  refine ⟨u,v,w,z,hb,norm_pos_iff.mpr (hb.1.2.ne_zero 0),huv,hvw,hz,humin,hvmin,hwmin,?_⟩
  intro R hR
  have hcount := original_norm_point_bound p hp κ t u v z hb huv hip R hR
  obtain ⟨h1,h2,h3⟩ := reciprocal_radii p hp κ t u v w z hb huv hvw hip hz hwmin R hR
  exact hcount.trans (Nat.mul_le_mul
    (Nat.mul_le_mul (by omega) (by omega)) (by omega))

end OriginalReciprocalMinimaRectangle318
