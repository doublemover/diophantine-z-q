module
public import ActualTwoDescentAllPlacesIntersection318
public section
noncomputable section
namespace ActualTwoDescentConcreteLocalObstruction318
set_option maxHeartbeats 16000000

open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentKummerHom318
open ActualTwoDescentLocalImageSubgroup318 ActualTwoDescentAllPlacesIntersection318
open ActualTwoDescentEllipticDoubleQuotient318 ActualTwoDescentEllipticModel318

/-- The actual rational Kummer image, as a subgroup of the actual all-place intersection. -/
def rationalImageInside (n : ℚ) (hn : n ≠ 0) : Subgroup (allPlacesImage n hn) :=
  (actualKummerImage n hn).comap (allPlacesImage n hn).subtype

/-- A concrete quotient measuring the remaining local-to-global obstruction.
No identification with a cohomological Tate-Shafarevich group is asserted. -/
abbrev LocalObstruction (n : ℚ) (hn : n ≠ 0) :=
  (allPlacesImage n hn) ⧸ rationalImageInside n hn

/-- Every actual rational E/2E class lands injectively in the actual all-place intersection. -/
def ellipticAllPlacesInjection (n : ℚ) (hn : n ≠ 0) : DoubleQuotient n →* allPlacesImage n hn where
  toFun q := ⟨ellipticKummerInjection n hn q,by
    apply actual_rational_image_le_all_places n hn
    refine QuotientGroup.induction_on q ?_
    intro P
    exact ⟨P,rfl⟩⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ x y)

lemma actual_all_places_injection_injective (n : ℚ) (hn : n ≠ 0) :
    Function.Injective (ellipticAllPlacesInjection n hn) := by
  intro x y h
  exact actual_elliptic_kummer_injective n hn (congrArg Subtype.val h)

lemma actual_all_places_injection_range (n : ℚ) (hn : n ≠ 0) :
    (ellipticAllPlacesInjection n hn).range=rationalImageInside n hn := by
  ext z
  constructor
  · rintro ⟨q,rfl⟩
    change ellipticKummerInjection n hn q ∈ actualKummerImage n hn
    refine QuotientGroup.induction_on q ?_
    intro P
    exact ⟨P,rfl⟩
  · intro hz
    obtain ⟨P,hP⟩ := (actual_kummer_image_iff n hn z.val).mp hz
    refine ⟨QuotientGroup.mk (Multiplicative.ofAdd P),?_⟩
    apply Subtype.ext
    exact hP

/-- Exact, actual membership criterion for the concrete obstruction class to vanish. -/
theorem actual_obstruction_zero_iff (n : ℚ) (hn : n ≠ 0) (z : allPlacesImage n hn) :
    (QuotientGroup.mk z : LocalObstruction n hn)=1 ↔
      ∃ P : Point n, kummerClass n hn P=z.val := by
  rw [QuotientGroup.eq_one_iff]
  exact actual_kummer_image_iff n hn z.val

/-- The full local-to-global assertion is equivalent to equality of these ACTUAL subgroups.
Neither side is assumed or proved unconditionally here. -/
theorem actual_all_obstructions_vanish_iff (n : ℚ) (hn : n ≠ 0) :
    (∀ z : allPlacesImage n hn, (QuotientGroup.mk z : LocalObstruction n hn)=1) ↔
      allPlacesImage n hn=actualKummerImage n hn := by
  constructor
  · intro h
    apply le_antisymm
    · intro z hz
      exact (actual_kummer_image_iff n hn z).mpr
        ((actual_obstruction_zero_iff n hn ⟨z,hz⟩).mp (h ⟨z,hz⟩))
    · exact actual_rational_image_le_all_places n hn
  · intro h z
    apply (actual_obstruction_zero_iff n hn z).mpr
    apply (actual_kummer_image_iff n hn z.val).mp
    rw [←h]
    exact z.property

end ActualTwoDescentConcreteLocalObstruction318
