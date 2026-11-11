module
public import ActualTwoDescentLocalImageSubgroup318
public section
noncomputable section
namespace ActualTwoDescentAllPlacesIntersection318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentSquareClassQuotient318
open ActualTwoDescentSquareClassFieldMap318 ActualTwoDescentLocalImageSubgroup318

local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _

/-- All finite prime places are indexed by actual Nat primes; the real place is included separately. -/
def allPlacesImage (n : ℚ) (hn : n ≠ 0) : Subgroup (SquareClass ℚ × SquareClass ℚ) where
  carrier := {z | z ∈ localImagePullback (algebraMap ℚ ℝ) n hn ∧
    ∀ (p : ℕ) [Fact p.Prime], z ∈ localImagePullback (algebraMap ℚ (ℚ_[p])) n hn}
  one_mem' := ⟨Subgroup.one_mem _,fun p _ => Subgroup.one_mem _⟩
  mul_mem' := by
    rintro x y ⟨hxR,hxp⟩ ⟨hyR,hyp⟩
    exact ⟨Subgroup.mul_mem _ hxR hyR,fun p _ => Subgroup.mul_mem _ (hxp p) (hyp p)⟩
  inv_mem' := by
    rintro x ⟨hxR,hxp⟩
    exact ⟨Subgroup.inv_mem _ hxR,fun p _ => Subgroup.inv_mem _ (hxp p)⟩

/-- Every actual rational Kummer image satisfies actual local-image membership at EVERY place. -/
theorem actual_rational_image_le_all_places (n : ℚ) (hn : n ≠ 0) :
    actualKummerImage n hn ≤ allPlacesImage n hn := by
  intro z hz
  exact ⟨actual_global_image_le_local_pullback (algebraMap ℚ ℝ) n hn hz,
    fun p _ => actual_global_image_le_local_pullback (algebraMap ℚ (ℚ_[p])) n hn hz⟩

/-- This concrete intersection is not asserted to have the dimension of the finite bad-place signature space. -/
lemma actual_all_places_iff (n : ℚ) (hn : n ≠ 0) (z : SquareClass ℚ × SquareClass ℚ) :
    z ∈ allPlacesImage n hn ↔
      (∃ P : Point ((algebraMap ℚ ℝ) n),
        ActualTwoDescentKummerHom318.kummerClass _ (field_map_ne_zero _ hn) P=
          squarePairMap (algebraMap ℚ ℝ) z) ∧
      ∀ (p : ℕ) [Fact p.Prime], ∃ P : Point ((algebraMap ℚ (ℚ_[p])) n),
        ActualTwoDescentKummerHom318.kummerClass _ (field_map_ne_zero _ hn) P=
          squarePairMap (algebraMap ℚ (ℚ_[p])) z := by
  constructor
  · rintro ⟨hR,hp⟩
    exact ⟨(actual_local_pullback_witness _ _ _ _).mp hR,
      fun p _ => (actual_local_pullback_witness _ _ _ _).mp (hp p)⟩
  · rintro ⟨hR,hp⟩
    exact ⟨(actual_local_pullback_witness _ _ _ _).mpr hR,
      fun p _ => (actual_local_pullback_witness _ _ _ _).mpr (hp p)⟩

end ActualTwoDescentAllPlacesIntersection318
