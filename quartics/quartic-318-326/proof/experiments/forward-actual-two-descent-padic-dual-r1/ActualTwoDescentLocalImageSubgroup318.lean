module
public import ActualTwoDescentKummerFieldNaturality318
public section
noncomputable section
namespace ActualTwoDescentLocalImageSubgroup318
set_option maxHeartbeats 16000000

open ActualTwoDescentEllipticModel318 ActualTwoDescentKummerHom318
open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentSquareClassFieldMap318
open ActualTwoDescentActualEllipticFieldMap318 ActualTwoDescentKummerFieldNaturality318
variable {K L : Type*} [Field K] [Field L] [CharZero K] [CharZero L]
variable [DecidableEq K] [DecidableEq L]

/-- Image of the actual elliptic group under the actual full Kummer homomorphism. -/
def actualKummerImage (n : K) (hn : n ≠ 0) : Subgroup (SquareClass K × SquareClass K) :=
  (kummerHom n hn).range

lemma actual_kummer_image_iff (n : K) (hn : n ≠ 0) (z : SquareClass K × SquareClass K) :
    z ∈ actualKummerImage n hn ↔ ∃ P : Point n, kummerClass n hn P=z := by
  constructor
  · rintro ⟨P,hP⟩
    exact ⟨P.toAdd,hP⟩
  · rintro ⟨P,hP⟩
    exact ⟨Multiplicative.ofAdd P,hP⟩

/-- Pullback of an actual field-local Kummer image, not a hypothetical coefficient condition. -/
def localImagePullback (f : K →+* L) (n : K) (hn : n ≠ 0) :
    Subgroup (SquareClass K × SquareClass K) :=
  (actualKummerImage (f n) (field_map_ne_zero f hn)).comap (squarePairMap f)

theorem actual_global_image_le_local_pullback (f : K →+* L) (n : K) (hn : n ≠ 0) :
    actualKummerImage n hn ≤ localImagePullback f n hn := by
  intro z hz
  obtain ⟨P,rfl⟩ := (actual_kummer_image_iff n hn z).mp hz
  apply (actual_kummer_image_iff (f n) (field_map_ne_zero f hn) _).mpr
  exact ⟨ellipticFieldMap f n hn P,actual_kummer_field_naturality f n hn P⟩

lemma actual_local_pullback_witness (f : K →+* L) (n : K) (hn : n ≠ 0)
    (z : SquareClass K × SquareClass K) :
    z ∈ localImagePullback f n hn ↔ ∃ P : Point (f n),
      kummerClass (f n) (field_map_ne_zero f hn) P=squarePairMap f z :=
  actual_kummer_image_iff (f n) (field_map_ne_zero f hn) _

end ActualTwoDescentLocalImageSubgroup318
