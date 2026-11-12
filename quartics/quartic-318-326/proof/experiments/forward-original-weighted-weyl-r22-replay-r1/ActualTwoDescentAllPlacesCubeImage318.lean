module
public import ActualTwoDescentActualCubeIndependence318
public section
noncomputable section
namespace ActualTwoDescentAllPlacesCubeImage318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentEightClassCube318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentLocalImageSubgroup318 ActualTwoDescentActualAllPlacesBound318

/-- The torsion generators are actual rational images; beta membership therefore
puts every candidate cube class in the ACTUAL all-place intersection. -/
lemma actual_cube_mem_all_places (n b : ℚ) (hn : n ≠ 0) (hb : b ≠ 0)
    (hbeta : retainedBetaClass b hb ∈ allPlacesImage n hn) (v : Cube) :
    cubeClass n b hn hb v ∈ allPlacesImage n hn := by
  have hfirst : firstTorsionClass n hn ∈ allPlacesImage n hn := by
    apply actual_rational_image_le_all_places n hn
    exact (actual_kummer_image_iff n hn _).mpr ⟨firstTorsion n hn,actual_first_torsion_class n hn⟩
  have hsecond : secondTorsionClass n hn ∈ allPlacesImage n hn := by
    apply actual_rational_image_le_all_places n hn
    exact (actual_kummer_image_iff n hn _).mpr ⟨torsionPoint n hn,actual_second_torsion_class n hn⟩
  exact (allPlacesImage n hn).mul_mem
    ((allPlacesImage n hn).mul_mem ((allPlacesImage n hn).pow_mem hsecond _)
      ((allPlacesImage n hn).pow_mem hfirst _)) ((allPlacesImage n hn).pow_mem hbeta _)

lemma actual_all_places_card_ge_eight (n b : ℚ) (hn : n ≠ 0) (hb : b ≠ 0)
    (hi : Function.Injective (cubeClass n b hn hb))
    (hbeta : retainedBetaClass b hb ∈ allPlacesImage n hn)
    [Finite (allPlacesImage n hn)] : 8 ≤ Nat.card (allPlacesImage n hn) := by
  let f : Cube → allPlacesImage n hn := fun v => ⟨cubeClass n b hn hb v,actual_cube_mem_all_places n b hn hb hbeta v⟩
  have hf : Function.Injective f := fun x y he => hi (congrArg Subtype.val he)
  simpa only [cube_card] using Nat.card_le_card_of_injective f hf

end ActualTwoDescentAllPlacesCubeImage318
