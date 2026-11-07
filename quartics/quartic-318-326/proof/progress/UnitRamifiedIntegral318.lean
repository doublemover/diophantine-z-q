module
public import UnitRamifiedPullback318
public section
noncomputable section
namespace UnitRamifiedIntegral318
open VerticalSection318 AlgebraicSectionPullback318 HorizontalIntegralCharts318
open SourceHorizontalSections318 UnitRamifiedPullback318 IsLocalRing
set_option maxHeartbeats 0
variable {R B K : Type*} [CommRing R] [CommRing B] [IsLocalRing B] [Algebra ℚ B]
  [Field K] [Algebra B K] [Algebra R K]

/-- The exact coefficient after extracting the single branch parameter is a
unit, without taking a square root of the original ramification unit. -/
theorem tangent_isUnit (u z du dz : B) (hu : IsUnit u)
    (hz : z ∈ maximalIdeal B) (hdz : IsUnit dz) : IsUnit (z*du+2*u*dz) := by
  apply (residue_ne_zero_iff_isUnit _).mp
  have hr : residue B z = 0 := (residue_eq_zero_iff z).mpr hz
  have hunit : IsUnit ((2:B)*u*dz) := by
    have htwo : IsUnit (2:B) := by simpa only [Int.cast_ofNat] using integer_isUnit (B := B) 2 (by norm_num)
    exact (htwo.mul hu).mul hdz
  simpa only [map_add,map_mul,hr,zero_mul,zero_add] using (hunit.map (residue B)).ne_zero

theorem branch_shift_unit (i : Fin 4) (w : B) (hw : residue B w = 0) :
    IsUnit (branchShift i w) := by
  apply IsUnit.prod_univ_iff.mpr
  intro j
  apply (residue_ne_zero_iff_isUnit _).mp
  simpa only [map_add,hw,add_zero] using
    ((difference_isUnit i j (Ne.symm j.property)).map (residue B)).ne_zero

theorem infinity_shift_unit (w : B) (hw : residue B w = 0) : IsUnit (infinityShift w) := by
  apply IsUnit.prod_univ_iff.mpr
  intro j
  apply (residue_ne_zero_iff_isUnit _).mp
  simp [hw]

theorem unit_fraction (n d : B) (hn : IsUnit n) (hd : IsUnit d) :
    ∃ b : B, IsUnit b ∧ algebraMap B K b = algebraMap B K n / algebraMap B K d := by
  obtain ⟨u,hu⟩ := hd
  refine ⟨n*(↑(u⁻¹):B),hn.mul (u⁻¹).isUnit,?_⟩
  rw [map_mul,map_units_inv,hu,div_eq_mul_inv]

theorem map_branchShift (i : Fin 4) (w : B) :
    algebraMap B K (branchShift i w) = branchShift i (algebraMap B K w) := by
  simp [branchShift]

theorem map_infinityShift (w : B) :
    algebraMap B K (infinityShift w) = infinityShift (algebraMap B K w) := by
  simp [infinityShift]

variable [IsDomain B] [IsFractionRing B K]

theorem finite_branch_sections (D : Derivation R K K)
    (preserves : ∀ b : B, ∃ c : B, D (algebraMap B K b) = algebraMap B K c)
    (i : Fin 4) (u z dz : B) (hu : IsUnit u) (hz : z ∈ maximalIdeal B) (hz0 : z ≠ 0)
    (hdz : IsUnit dz) (hDz : D (algebraMap B K z) = algebraMap B K dz) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 D ((contacts i : K)+algebraMap B K u*(algebraMap B K z)^2) ∧
      algebraMap B K c1 = section1 D ((contacts i : K)+algebraMap B K u*(algebraMap B K z)^2) := by
  apply scale_integral_pair
  obtain ⟨du,hDu⟩ := preserves u
  let c : B := z*du+2*u*dz
  have hc : IsUnit c := tangent_isUnit u z du dz hu hz hdz
  have hmapc : algebraMap B K c = tangentFactor D (algebraMap B K u) (algebraMap B K z) := by
    simp only [c,tangentFactor,map_add,map_mul,map_ofNat,hDu,hDz]
  have hr : residue B (u*z^2) = 0 := by
    simp only [map_mul,map_pow,(residue_eq_zero_iff z).mpr hz,zero_pow (by decide : 2 ≠ 0),mul_zero]
  have hden := branch_shift_unit i (u*z^2) hr
  obtain ⟨b0,hb0,he⟩ := unit_fraction (K := K) (c^2) (u*branchShift i (u*z^2)) (hc.pow 2) (hu.mul hden)
  have huK : algebraMap B K u ≠ 0 := (hu.map (algebraMap B K)).ne_zero
  have hzK : algebraMap B K z ≠ 0 := fun h => hz0 ((IsFractionRing.injective B K) (by simpa using h))
  have h0 : algebraMap B K b0 = coefficient0 D ((contacts i : K)+algebraMap B K u*(algebraMap B K z)^2) := by
    rw [(UnitRamifiedPullback318.finite_coefficients D i _ _ huK hzK).1]
    simpa only [map_pow,map_mul,map_branchShift,hmapc] using he
  refine ⟨b0,((contacts i:B)+u*z^2)*b0,Or.inl hb0,h0,?_⟩
  simp only [map_mul,map_add,map_intCast,map_pow,h0,coefficient1]

theorem infinity_sections (D : Derivation R K K)
    (preserves : ∀ b : B, ∃ c : B, D (algebraMap B K b) = algebraMap B K c)
    (u z dz : B) (hu : IsUnit u) (hz : z ∈ maximalIdeal B) (hz0 : z ≠ 0)
    (hdz : IsUnit dz) (hDz : D (algebraMap B K z) = algebraMap B K dz) :
    ∃ c0 c1 : B, (IsUnit c0 ∨ IsUnit c1) ∧
      algebraMap B K c0 = section0 D (1/(algebraMap B K u*(algebraMap B K z)^2)) ∧
      algebraMap B K c1 = section1 D (1/(algebraMap B K u*(algebraMap B K z)^2)) := by
  apply scale_integral_pair
  obtain ⟨du,hDu⟩ := preserves u
  let c : B := z*du+2*u*dz
  have hc : IsUnit c := tangent_isUnit u z du dz hu hz hdz
  have hmapc : algebraMap B K c = tangentFactor D (algebraMap B K u) (algebraMap B K z) := by
    simp only [c,tangentFactor,map_add,map_mul,map_ofNat,hDu,hDz]
  have hr : residue B (u*z^2) = 0 := by
    simp only [map_mul,map_pow,(residue_eq_zero_iff z).mpr hz,zero_pow (by decide : 2 ≠ 0),mul_zero]
  have hden := infinity_shift_unit (u*z^2) hr
  obtain ⟨b1,hb1,he⟩ := unit_fraction (K := K) (c^2) (u*infinityShift (u*z^2)) (hc.pow 2) (hu.mul hden)
  have huK : algebraMap B K u ≠ 0 := (hu.map (algebraMap B K)).ne_zero
  have hzK : algebraMap B K z ≠ 0 := fun h => hz0 ((IsFractionRing.injective B K) (by simpa using h))
  have hwK : algebraMap B K u*(algebraMap B K z)^2 ≠ 0 := mul_ne_zero huK (pow_ne_zero _ hzK)
  have h1 : algebraMap B K b1 = coefficient1 D (1/(algebraMap B K u*(algebraMap B K z)^2)) := by
    rw [(UnitRamifiedPullback318.infinity_coefficients D _ _ huK hzK).2]
    simpa only [map_pow,map_mul,map_infinityShift,hmapc] using he
  refine ⟨(u*z^2)*b1,b1,Or.inr hb1,?_,h1⟩
  rw [map_mul,map_mul,map_pow,h1,coefficient1]
  rw [←mul_assoc,mul_one_div_cancel hwK,one_mul]

end UnitRamifiedIntegral318
