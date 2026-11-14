module
public import ActualTwoDescentObstructionVanishing318
public section
noncomputable section
namespace ActualTwoDescentBetaGeneratesRationalImage318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentActualTorsionPoint318
open ActualTwoDescentEightClassCube318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentLocalImageSubgroup318 ActualTwoDescentActualAllPlacesBound318
open ActualTwoDescentPrimeMonomials318 ActualTwoDescentFiniteConclusion318
open scoped BigOperators

lemma actual_cube_mem_rational_image (n b : ℚ) (hn : n ≠ 0) (hb : b ≠ 0)
    (hbeta : retainedBetaClass b hb ∈ actualKummerImage n hn) (v : Cube) :
    cubeClass n b hn hb v ∈ actualKummerImage n hn := by
  have hfirst : firstTorsionClass n hn ∈ actualKummerImage n hn :=
    (actual_kummer_image_iff n hn _).mpr ⟨firstTorsion n hn,actual_first_torsion_class n hn⟩
  have hsecond : secondTorsionClass n hn ∈ actualKummerImage n hn :=
    (actual_kummer_image_iff n hn _).mpr ⟨torsionPoint n hn,actual_second_torsion_class n hn⟩
  exact (actualKummerImage n hn).mul_mem
    ((actualKummerImage n hn).mul_mem ((actualKummerImage n hn).pow_mem hsecond _)
      ((actualKummerImage n hn).pow_mem hfirst _)) ((actualKummerImage n hn).pow_mem hbeta _)

/-- A represented beta class generates the entire actual all-place group with the two rational torsion classes. -/
theorem actual_beta_image_implies_local_global {U : Type*} [Fintype U] [DecidableEq U]
    (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (hp2 : ∀ i, p i ≠ 2) (hp3 : ∀ i, p i ≠ 3)
    (a beta : Option U → ZMod 2) (N : ℕ) (C : Conclusion p a beta N)
    (hn : (∏ i, p i) ≠ 0) (hb : monomial p beta ≠ 0)
    (hbeta : retainedBetaClass (monomial p beta : ℚ) (Nat.cast_ne_zero.mpr hb) ∈
      actualKummerImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn)) :
    allPlacesImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn)=
      actualKummerImage ((∏ i, p i : ℕ) : ℚ) (Nat.cast_ne_zero.mpr hn) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨v,hv⟩ := actual_all_places_cube_bound p hd hp2 hp3 a beta N C hn hb ⟨z,hz⟩
    rw [hv]
    exact actual_cube_mem_rational_image _ _ _ _ hbeta v
  · exact actual_rational_image_le_all_places _ _

end ActualTwoDescentBetaGeneratesRationalImage318
