module
public import ActualTwoDescentConcreteLocalObstruction318
public section
noncomputable section
namespace ActualTwoDescentBetaObstructionConsumer318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentEightClassCube318
open ActualTwoDescentBetaNonexceptional318 ActualTwoDescentPointExtraction318
open ActualTwoDescentEllipticPointExtraction318 ActualTwoDescentLocalImageSubgroup318
open ActualTwoDescentAllPlacesIntersection318 ActualTwoDescentConcreteLocalObstruction318

/-- If the actual beta class lies in the actual rational image, cube independence
excludes the exceptional torsion points and recovers the original rational Kummer witness. -/
theorem actual_beta_point_of_global_image (n b : ℚ) (hn : n ≠ 0) (hb : b ≠ 0)
    (hi : Function.Injective (cubeClass n b hn hb))
    (H : retainedBetaClass b hb ∈ actualKummerImage n hn) :
    Nonempty (KummerPoint b n) := by
  obtain ⟨P,hP⟩ := (actual_kummer_image_iff n hn _).mp H
  have hcube : kummerClass n hn P=cubeClass n b hn hb (0,0,1) := by
    simpa [cubeClass] using hP
  obtain ⟨x,y,h,hxy,hx,hB,hA⟩ := actual_beta_nonexceptional n b hn hb hi P hcube
  subst P
  obtain ⟨Q,_,_⟩ := actual_kummer_point_of_elliptic_class n b x y hn hb h hx hA hB hP
  exact ⟨Q⟩

/-- A literal vanishing obstruction class, not just local solubility, supplies the rational point. -/
theorem actual_beta_point_of_obstruction_vanishes (n b : ℚ) (hn : n ≠ 0) (hb : b ≠ 0)
    (hi : Function.Injective (cubeClass n b hn hb))
    (hloc : retainedBetaClass b hb ∈ allPlacesImage n hn)
    (hobs : (QuotientGroup.mk ⟨retainedBetaClass b hb,hloc⟩ : LocalObstruction n hn)=1) :
    Nonempty (KummerPoint b n) := by
  apply actual_beta_point_of_global_image n b hn hb hi
  exact (actual_kummer_image_iff n hn _).mpr
    ((actual_obstruction_zero_iff n hn ⟨retainedBetaClass b hb,hloc⟩).mp hobs)

end ActualTwoDescentBetaObstructionConsumer318
