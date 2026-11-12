module
public import OriginalBasisDeterminantIndex318
public section
noncomputable section
namespace OriginalGoodLatticeVolumeBound318
open scoped RealInnerProductSpace
open TernaryQuadraticLineCover318 LiteralTernaryReduction318 OriginalEuclideanLattice318
open OriginalControlledIntegralBasis318 OriginalCofactorCoordinates318
open OriginalAnisotropicRectangle318 OriginalThirdMinimumTail318
open OriginalReciprocalMinimaRectangle318 OriginalBasisDeterminantIndex318
open OriginalIntegerNormalProjection318
set_option maxHeartbeats 5000000
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma actual_determinant_upper (u v w z : Vector ℤ) (hz : ‖embed z‖≤2*‖embed w‖) :
    |(determinant u v z:ℝ)|≤2*(‖embed u‖*‖embed v‖*‖embed w‖) := by
  have he : ⟪embed (normal u v),embed z⟫=(determinant u v z:ℝ) := inner_embed _ _
  have hc := abs_real_inner_le_norm (embed (normal u v)) (embed z)
  rw [he] at hc
  calc
    _ ≤ ‖embed (normal u v)‖*‖embed z‖ := hc
    _ ≤ (‖embed u‖*‖embed v‖)*(2*‖embed w‖) :=
      mul_le_mul (cross_norm_le u v) hz (norm_nonneg _) (by positivity)
    _ = _ := by ring

lemma scaled_floor_factor (R L k : ℝ) (hL : 0<L) (hLR : L≤R) (hk : 0≤k) :
    (2*(floorRadius (k*R/L):ℝ)+1)*L≤(2*k+1)*R := by
  have hR : 0≤R := hL.le.trans hLR
  have hf := floorRadius_le (k*R/L) (by positivity)
  have hf' := (le_div_iff₀ hL).mp hf
  nlinarith

/-- Uniform volume-order count once the actual THIRD minimum is within
R. The index M² is consumed at this exact whole basis, and integer
boundary terms are bounded using R>=lambda3, NOT the stronger R>=M. -/
theorem good_lattice_count (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) (u v w z : Vector ℤ)
    (hb : IntegralBasisTriple p κ t u v z)
    (huv : ‖embed u‖≤‖embed v‖) (hvw : ‖embed v‖≤‖embed w‖)
    (hip : |⟪embed u,embed v⟫|≤‖embed u‖^2/2) (hz : ‖embed z‖≤2*‖embed w‖)
    (hwmin : ∀ y : Vector ℤ, y∈literalLattice p κ t →
      embed y∉Submodule.span ℝ (Set.range ![embed u,embed v]) → ‖embed w‖≤‖embed y‖)
    (R : ℝ) (hWR : ‖embed w‖≤R) :
    (Nat.card (NormPoints p κ t R):ℝ)*(FixedSquarefreeCRT318.modulus p:ℝ)^2≤5202*R^3 := by
  have hU : 0<‖embed u‖ := norm_pos_iff.mpr (hb.1.2.ne_zero 0)
  have hV : 0<‖embed v‖ := hU.trans_le huv
  have hW : 0<‖embed w‖ := hV.trans_le hvw
  have hR : 0≤R := hW.le.trans hWR
  let A := 2*floorRadius (8*R/‖embed u‖)+1
  let B := 2*floorRadius (8*R/‖embed v‖)+1
  let C := 2*floorRadius (4*R/‖embed w‖)+1
  have hcount := original_norm_point_bound p hp κ t u v z hb huv hip R hR
  obtain ⟨h1,h2,h3⟩ := reciprocal_radii p hp κ t u v w z hb huv hvw hip hz hwmin R hR
  have hcount' : Nat.card (NormPoints p κ t R)≤A*B*C :=
    hcount.trans (Nat.mul_le_mul (Nat.mul_le_mul (by dsimp [A];omega) (by dsimp [B];omega))
      (by dsimp [C];omega))
  have hA : (A:ℝ)*‖embed u‖≤17*R := by
    simpa only [A,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,show (2:ℝ)*8+1=17 by norm_num] using
      scaled_floor_factor R ‖embed u‖ 8 hU (huv.trans (hvw.trans hWR)) (by norm_num)
  have hB : (B:ℝ)*‖embed v‖≤17*R := by
    simpa only [B,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,show (2:ℝ)*8+1=17 by norm_num] using
      scaled_floor_factor R ‖embed v‖ 8 hV (hvw.trans hWR) (by norm_num)
  have hC : (C:ℝ)*‖embed w‖≤9*R := by
    simpa only [C,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,show (2:ℝ)*4+1=9 by norm_num] using
      scaled_floor_factor R ‖embed w‖ 4 hW hWR (by norm_num)
  have hAB := mul_le_mul hA hB (by positivity) (by positivity)
  have hABC := mul_le_mul hAB hC (by positivity) (by positivity)
  have hmass : ((A*B*C:ℕ):ℝ)*(‖embed u‖*‖embed v‖*‖embed w‖)≤2601*R^3 := by
    push_cast
    nlinarith only [hABC]
  have hindex : (FixedSquarefreeCRT318.modulus p:ℝ)^2≤
      2*(‖embed u‖*‖embed v‖*‖embed w‖) := by
    rw [←actual_basis_determinant_index p hp hd hp2 κ t u v z hb]
    exact actual_determinant_upper u v w z hz
  have hcountR : (Nat.card (NormPoints p κ t R):ℝ)≤((A*B*C:ℕ):ℝ) := by exact_mod_cast hcount'
  calc
    _ ≤ ((A*B*C:ℕ):ℝ)*(FixedSquarefreeCRT318.modulus p:ℝ)^2 :=
      mul_le_mul_of_nonneg_right hcountR (sq_nonneg _)
    _ ≤ ((A*B*C:ℕ):ℝ)*(2*(‖embed u‖*‖embed v‖*‖embed w‖)) :=
      mul_le_mul_of_nonneg_left hindex (Nat.cast_nonneg _)
    _ ≤ 5202*R^3 := by nlinarith only [hmass]

/-- The controlled good-lattice volume estimate with the whole basis and
all shortest-vector witnesses PRODUCED on the actual original lattice. -/
theorem actual_good_lattice_volume (p : ι → ℕ) (hp : ∀ i, (p i).Prime)
    (hd : Function.Injective p) (hp2 : ∀ i, p i≠2) (κ : ℤ)
    (t : ∀ i, Option (ZMod (p i))) :
    ∃ u v w z : Vector ℤ, IntegralBasisTriple p κ t u v z ∧
      OriginalAttainedMinima318.IndependentTriple p κ t ![u,v,w] ∧
      ‖embed u‖≤‖embed v‖ ∧ ‖embed v‖≤‖embed w‖ ∧
      ∀ R : ℝ, ‖embed w‖≤R →
        (Nat.card (NormPoints p κ t R):ℝ)*(FixedSquarefreeCRT318.modulus p:ℝ)^2≤5202*R^3 := by
  obtain ⟨u,v,w,z,hi,hb,huv,hvw,hip,hz,humin,hvmin,hwmin⟩ := actual_controlled_basis p hp κ t
  exact ⟨u,v,w,z,hb,hi,huv,hvw,
    fun R hR => good_lattice_count p hp hd hp2 κ t u v w z hb huv hvw hip hz hwmin R hR⟩

end OriginalGoodLatticeVolumeBound318
