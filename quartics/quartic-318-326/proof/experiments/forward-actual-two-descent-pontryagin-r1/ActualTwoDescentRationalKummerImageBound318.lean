module
public import ActualTwoDescentEightClassCube318
public section
noncomputable section
namespace ActualTwoDescentRationalKummerImageBound318
set_option maxHeartbeats 16000000
variable {K : Type*} [Field K] [CharZero K]


open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentLiteralKummerClasses318
open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentEightClassCube318 ActualTwoDescentSameRationalBounds318
open ActualTwoDescentRationalPointPlaces318

/-- The earlier necessary rational-point bound now bounds the image of the
ACTUAL full Kummer homomorphism, including all exceptional points. -/
theorem actual_rational_image_bound (n b : ℕ) (hn : n ≠ 0) (hb : b ≠ 0)
    (H : RationalEightBound n b) (P : Point (n : ℚ)) :
    ∃ v : Cube, kummerClass (n : ℚ) (by exact_mod_cast hn) P=
      cubeClass (n : ℚ) (b : ℚ) (by exact_mod_cast hn) (by exact_mod_cast hb) v := by
  let hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  let hbq : (b : ℚ) ≠ 0 := by exact_mod_cast hb
  cases P with
  | zero =>
    exact ⟨(0,0,0),by simp [kummer_class_zero,cubeClass]⟩
  | some x y h =>
    have hc := (curve_equation (n : ℚ) x y).mp h.left
    by_cases hx : x=0
    · have hy : y=0 := by
        apply (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
        rw [hc,hx]
        ring
      subst x; subst y
      refine ⟨(1,1,0),?_⟩
      change kummerClass (n : ℚ) hnq (zeroTorsion (n : ℚ) hnq)=_
      rw [actual_zero_torsion_class]
      simp [cubeClass]
    by_cases hB : x-(n : ℚ)=0
    · have hxn : x=(n : ℚ) := sub_eq_zero.mp hB
      have hy : y=0 := by
        apply (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
        rw [hc,hB]
        ring
      subst x; subst y
      refine ⟨(0,1,0),?_⟩
      change kummerClass (n : ℚ) hnq (firstTorsion (n : ℚ) hnq)=_
      rw [actual_first_torsion_class]
      simp [cubeClass]
    by_cases hA : x+3*(n : ℚ)=0
    · have hxn : x= -3*(n : ℚ) := by linear_combination hA
      have hy : y=0 := by
        apply (pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp
        rw [hc,hA]
        ring
      subst x; subst y
      refine ⟨(1,0,0),?_⟩
      change kummerClass (n : ℚ) hnq (torsionPoint (n : ℚ) hnq)=_
      rw [actual_second_torsion_class]
      simp [cubeClass]
    let R : RationalPoint n := ⟨x,y,hx,hB,hA,hc⟩
    obtain ⟨ε,c,e,r,s,hr,hs,hR,hS⟩ := H R
    refine ⟨(ε,c,e),?_⟩
    rw [actual_cube_literal]
    apply (actual_kummer_pair_iff (n : ℚ) x y _ _ hnq h hA hB _ _).mpr
    exact ⟨r,s,hr,hs,hR,hS⟩

end ActualTwoDescentRationalKummerImageBound318
