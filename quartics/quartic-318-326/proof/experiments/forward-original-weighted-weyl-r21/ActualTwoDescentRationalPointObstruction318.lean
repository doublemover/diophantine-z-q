module
public import ActualTwoDescentBetaObstructionConsumer318
public section
noncomputable section
namespace ActualTwoDescentRationalPointObstruction318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentEightClassCube318
open ActualTwoDescentLiteralKummerClasses318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentPointExtraction318 ActualTwoDescentLocalImageSubgroup318
open ActualTwoDescentAllPlacesIntersection318 ActualTwoDescentConcreteLocalObstruction318
open ActualTwoDescentBetaObstructionConsumer318

/-- An original rational Kummer witness really represents the retained beta class in the actual group. -/
theorem actual_global_image_of_kummer_point (n b : ℚ) (hn : n ≠ 0) (hb : b ≠ 0)
    (P : KummerPoint b n) : retainedBetaClass b hb ∈ actualKummerImage n hn := by
  have hA : P.x+3*n ≠ 0 := by rw [P.first]; exact mul_ne_zero hb (pow_ne_zero _ P.u_ne)
  have hB : P.x-n ≠ 0 := by rw [P.second]; exact pow_ne_zero _ P.v_ne
  have h := curve_nonsingular n P.x P.y hn P.curve
  apply (actual_kummer_image_iff n hn _).mpr
  refine ⟨.some P.x P.y h,?_⟩
  have hp := (actual_kummer_pair_iff n P.x P.y b 1 hn h hA hB hb one_ne_zero).mpr
    ⟨P.u,P.v,P.u_ne,P.v_ne,P.first,by simpa only [one_mul] using P.second⟩
  simpa only [class_of_one,retainedBetaClass] using hp

/-- This is an exact iff for the actual rational point target, not a local-solubility substitution. -/
theorem actual_rational_kummer_iff_obstruction (n b : ℚ) (hn : n ≠ 0) (hb : b ≠ 0)
    (hi : Function.Injective (cubeClass n b hn hb)) :
    Nonempty (KummerPoint b n) ↔ ∃ hloc : retainedBetaClass b hb ∈ allPlacesImage n hn,
      (QuotientGroup.mk ⟨retainedBetaClass b hb,hloc⟩ : LocalObstruction n hn)=1 := by
  constructor
  · rintro ⟨P⟩
    have hg := actual_global_image_of_kummer_point n b hn hb P
    refine ⟨actual_rational_image_le_all_places n hn hg,?_⟩
    exact (QuotientGroup.eq_one_iff _).mpr hg
  · rintro ⟨hloc,hobs⟩
    exact actual_beta_point_of_obstruction_vanishes n b hn hb hi hloc hobs

end ActualTwoDescentRationalPointObstruction318
