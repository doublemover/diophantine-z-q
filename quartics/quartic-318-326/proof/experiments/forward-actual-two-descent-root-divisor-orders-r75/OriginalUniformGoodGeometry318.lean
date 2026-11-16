module
public import OriginalGoodAllPrimeFamily318
public section
noncomputable section
namespace OriginalUniformGoodGeometry318
open TernaryQuadraticLineCover318 OriginalEuclideanLattice318 OriginalSieveFrame318
open OriginalAnisotropicRectangle318 OriginalGoodLatticeVolumeBound318
open OriginalBasisDeterminantIndex318 OriginalReducedRectangleVolume318
set_option maxHeartbeats 7500000

variable (κ t : ℤ)
  (s : ∀ k : LiteralSliceModulus318.PrimeIndex κ t,
    Option (ZMod (LiteralSliceModulus318.prime κ t k)))
  (d : Frame (LiteralSliceModulus318.prime κ t) κ s)

lemma index_upper : (LiteralSliceModulus318.modulus κ t:ℝ)^2≤
    2*(‖embed d.u‖*‖embed d.v‖*‖embed d.w‖) := by
  rw [←actual_basis_determinant_index (LiteralSliceModulus318.prime κ t)
    (LiteralSliceModulus318.prime_is_prime κ t) (LiteralSliceModulus318.prime_injective κ t)
    (LiteralSliceModulus318.prime_odd κ t) κ s d.u d.v d.z d.basis]
  exact actual_determinant_upper d.u d.v d.w d.z d.last_bound

lemma radius_scaled (R : ℝ) (hR : 0≤R) :
    (d.firstRadius R:ℝ)*‖embed d.u‖≤8*R ∧
    (d.secondRadius R:ℝ)*‖embed d.v‖≤8*R ∧
    (d.thirdRadius R:ℝ)*‖embed d.w‖≤4*R := by
  have hU : 0<‖embed d.u‖ := norm_pos_iff.mpr (d.basis.1.2.ne_zero 0)
  have hV := hU.trans_le d.first_second
  have hW := hV.trans_le d.second_third
  exact ⟨(le_div_iff₀ hU).mp (floorRadius_le _ (by positivity)),
    (le_div_iff₀ hV).mp (floorRadius_le _ (by positivity)),
    (le_div_iff₀ hW).mp (floorRadius_le _ (by positivity))⟩

/-- Integer floor and boundary terms for the ACTUAL enlarged25-shear
rectangles. Scaled widths49R,49R,9R retain the original anisotropy. -/
lemma enlarged_scaled (R : ℝ) (hWR : ‖embed d.w‖≤R) :
    (2*((d.firstRadius R+4*d.thirdRadius R:ℕ):ℝ)+1)*‖embed d.u‖≤49*R ∧
    (2*((d.secondRadius R+4*d.thirdRadius R:ℕ):ℝ)+1)*‖embed d.v‖≤49*R ∧
    (2*(d.thirdRadius R:ℝ)+1)*‖embed d.w‖≤9*R := by
  have hU : 0<‖embed d.u‖ := norm_pos_iff.mpr (d.basis.1.2.ne_zero 0)
  have hV := hU.trans_le d.first_second
  have hW := hV.trans_le d.second_third
  have hUR := d.first_second.trans (d.second_third.trans hWR)
  have hVR := d.second_third.trans hWR
  have hR : 0≤R := hW.le.trans hWR
  have ha := scaled_floor_factor R ‖embed d.u‖ 8 hU hUR (by norm_num)
  have hb := scaled_floor_factor R ‖embed d.v‖ 8 hV hVR (by norm_num)
  have hc := scaled_floor_factor R ‖embed d.w‖ 4 hW hWR (by norm_num)
  have hcs := (radius_scaled κ t s d R hR).2.2
  have hcu := mul_le_mul_of_nonneg_left (d.first_second.trans d.second_third)
    (show 0≤(d.thirdRadius R:ℝ) by positivity)
  have hcv := mul_le_mul_of_nonneg_left d.second_third
    (show 0≤(d.thirdRadius R:ℝ) by positivity)
  change (2*(d.firstRadius R:ℝ)+1)*‖embed d.u‖≤17*R at ha
  change (2*(d.secondRadius R:ℝ)+1)*‖embed d.v‖≤17*R at hb
  change (2*(d.thirdRadius R:ℝ)+1)*‖embed d.w‖≤9*R at hc
  refine ⟨?_,?_,hc⟩ <;> push_cast <;> nlinarith only [ha,hb,hcs,hcu,hcv]

/-- Same original index M² consumes all three minima. Thus the large
prime area and zero-cylinder terms cost R²T, not an extra source dimension.
This uses only W<=T and W<=R, not the stronger R>=M. -/
theorem original_area_cylinder (R T : ℝ) (hWR : ‖embed d.w‖≤R) (hWT : ‖embed d.w‖≤T) :
    let A := d.firstRadius R+4*d.thirdRadius R
    let B := d.secondRadius R+4*d.thirdRadius R
    let C := d.thirdRadius R
    ((2*A+1:ℕ):ℝ)*(2*B+1)*(LiteralSliceModulus318.modulus κ t:ℝ)^2≤4802*R^2*T ∧
    (((2*A+1:ℕ):ℝ)+(2*B+1))*(2*C+1)*(LiteralSliceModulus318.modulus κ t:ℝ)^2≤1764*R^2*T := by
  let a : ℝ := 2*((d.firstRadius R:ℝ)+4*(d.thirdRadius R:ℝ))+1
  let b : ℝ := 2*((d.secondRadius R:ℝ)+4*(d.thirdRadius R:ℝ))+1
  let c : ℝ := 2*(d.thirdRadius R:ℝ)+1
  have ha0 : 0≤a := by dsimp [a];positivity
  have hb0 : 0≤b := by dsimp [b];positivity
  have hc0 : 0≤c := by dsimp [c];positivity
  have hR : 0≤R := (norm_nonneg _).trans hWR
  have hT : 0≤T := (norm_nonneg _).trans hWT
  obtain ⟨ha,hb,hc⟩ := enlarged_scaled κ t s d R hWR
  push_cast at ha hb
  have hm := index_upper κ t s d
  have hab := mul_le_mul ha hb (by positivity) (by positivity)
  have habW := mul_le_mul hab hWT (norm_nonneg _) (by positivity)
  have harea := mul_le_mul_of_nonneg_left hm (mul_nonneg ha0 hb0)
  have hVT := d.second_third.trans hWT
  have hUT := d.first_second.trans hVT
  have hac := mul_le_mul ha hc (by positivity) (by positivity)
  have hbc := mul_le_mul hb hc (by positivity) (by positivity)
  have hacV := mul_le_mul hac hVT (norm_nonneg _) (by positivity)
  have hbcU := mul_le_mul hbc hUT (norm_nonneg _) (by positivity)
  have hcyl := mul_le_mul_of_nonneg_left hm (mul_nonneg (add_nonneg ha0 hb0) hc0)
  dsimp only
  push_cast
  change a*b*(LiteralSliceModulus318.modulus κ t:ℝ)^2≤4802*R^2*T ∧
    (a+b)*c*(LiteralSliceModulus318.modulus κ t:ℝ)^2≤1764*R^2*T
  change a*‖embed d.u‖*(b*‖embed d.v‖)*‖embed d.w‖≤(49*R)*(49*R)*T at habW
  change a*‖embed d.u‖*(c*‖embed d.w‖)*‖embed d.v‖≤(49*R)*(9*R)*T at hacV
  change b*‖embed d.v‖*(c*‖embed d.w‖)*‖embed d.u‖≤(49*R)*(9*R)*T at hbcU
  constructor
  · nlinarith only [harea,habW]
  · nlinarith only [hcyl,hacV,hbcU]

end OriginalUniformGoodGeometry318
