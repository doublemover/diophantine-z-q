module
public import PELOriginalCharacterProjection318
public import OriginalContactInertiaBasis318
public section
noncomputable section
namespace PELOriginalContactCharacterIdentity318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318
open FourBinaryCharacters318 OriginalContactInertiaBasis318
set_option maxHeartbeats 1200000

/-- Exact comparison of the analytic PRIME character with the original
contact complementary-root character. In particular, no permutation of the
four quotient factors is silently inserted at reconstruction. -/
lemma rational_character : ∀ (i : Fin 4) (g : Labels),
    complementary (F := ℚ) i (basis g) =
      if Multiplicative.toAdd g i = 0 then 1 else -1 := by decide

lemma original_kernel_iff (i : Fin 4) (g : Labels) :
    g ∈ (character i).ker ↔ complementary (F := ℚ) i (basis g) = 1 := by
  change character i g = 1 ↔ _
  rw [rational_character]
  have hc : character i g = 1 ↔ Multiplicative.toAdd g i = 0 := Iff.rfl
  rw [hc]
  by_cases h : Multiplicative.toAdd g i = 0 <;> simp [h]

/-- Equality of WHOLE original subgroups, not just agreement on the five
inertia generators. This identifies the actual analytic orbit relation with
the exact original complementary-character kernel used by field reconstruction. -/
lemma original_kernel (i : Fin 4) :
    ((character i).ker : Set Labels) =
      {g | complementary (F := ℚ) i (basis g) = 1} := by
  ext g
  exact original_kernel_iff i g

variable {F : Type*} [Field F] [CharZero F]
lemma coordinate_cast (i : Fin 4) (g : Group) :
    algebraMap ℚ F (coordinate (F := ℚ) i g) = coordinate (F := F) i g := by
  unfold coordinate
  split <;> simp

lemma complementary_cast (i : Fin 4) (g : Group) :
    algebraMap ℚ F (complementary (F := ℚ) i g) = complementary (F := F) i g := by
  simp only [complementary,MonoidHom.coe_mk,OneHom.coe_mk,map_prod,coordinate_cast]

/-- The same identity holds in the actual characteristic-zero contact
function field, with its original rational coefficient map retained. -/
lemma field_character (i : Fin 4) (g : Labels) :
    complementary (F := F) i (basis g) =
      if Multiplicative.toAdd g i = 0 then 1 else -1 := by
  rw [← complementary_cast,rational_character]
  split <;> simp

/-- All original complementary character kernels coincide before and after
passing to a characteristic-zero field; no scalar sign collapse is allowed. -/
lemma field_kernel_iff (i : Fin 4) (g : Labels) :
    g ∈ (character i).ker ↔ complementary (F := F) i (basis g) = 1 := by
  constructor
  · intro h
    rw [← complementary_cast,(original_kernel_iff i g).mp h,map_one]
  · intro h
    apply (original_kernel_iff i g).mpr
    apply (algebraMap ℚ F).injective
    simpa only [map_one,complementary_cast] using h
end PELOriginalContactCharacterIdentity318
