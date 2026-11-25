module

public import OriginalYuanAllFinitePlaces318
public import ContactRadical318
public import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

@[expose] public section
noncomputable section

namespace OriginalLiteralFiveContactAllFinite318

open OriginalYuanMarkedSectionEvaluation318
open OriginalFineArithmeticPlaceSwitch318 OriginalThreeElevenNamedProperCentres318
open OriginalYuanAllFinitePlaces318 SectionHeight318 NumberField

variable {E : Type*} [Field E] [CharZero E]

/-- Exactly the original normalized T from primitive u:v, as used
in the unchanged MetricSections ratio, not the sharp t/32 pair. -/
def literalT (u v : ℤ) : E := ((32*((u:ℚ)/(v:ℚ)):ℚ):E)

theorem literal_poles_excluded (u v : ℤ)
    (noncontact : ∀ j : Fin 5,ContactRadical318.forms u v j ≠ 0) :
    P (literalT (E:=E) u v)≠0 := by
  have hv : (v:E)≠0 := by exact_mod_cast (noncontact 0 : v≠0)
  have hu : (u:E)≠0 := by exact_mod_cast (noncontact 1 : u≠0)
  have h₁ : (u:E)-(v:E)≠0 := by exact_mod_cast (noncontact 2 : u-v≠0)
  have h₂ : (u:E)-2401*(v:E)≠0 := by exact_mod_cast (noncontact 3 : u-2401*v≠0)
  have h₃ : 32*(u:E)+343*(v:E)≠0 := by exact_mod_cast (noncontact 4 : 32*u+343*v≠0)
  have n32 : (32:E)≠0 := by norm_num
  have r : literalT (E:=E) u v=32*((u:E)/(v:E)) := by
    simp only [literalT,Rat.cast_mul,Rat.cast_div,Rat.cast_intCast,Rat.cast_ofNat]
  have r₁ : literalT (E:=E) u v-32=32*((u:E)-(v:E))/(v:E) := by
    rw [r]; field_simp [hv] <;> ring
  have r₂ : literalT (E:=E) u v-76832=32*((u:E)-2401*(v:E))/(v:E) := by
    rw [r]; field_simp [hv] <;> ring
  have r₃ : literalT (E:=E) u v+343=(32*(u:E)+343*(v:E))/(v:E) := by
    rw [r]; field_simp [hv] <;> ring
  unfold P
  rw [r₁,r₂,r₃,r]
  exact mul_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero n32 (div_ne_zero hu hv))
      (div_ne_zero (mul_ne_zero n32 h₁) hv)) (div_ne_zero (mul_ne_zero n32 h₂) hv))
    (div_ne_zero h₃ hv)

universe u
variable {F : Type u} [Field F] [NumberField F]
variable (B : OriginalFineBases.{u}) (m : CommonMark (E:=F) B)
variable (HN CN : FrameNorms F)
variable {H₀ C₀ : Type u}
  [AddCommGroup H₀] [AddCommGroup C₀] [Module F H₀] [Module F C₀]
variable {H C : Lane→Type u}
  [∀ n,AddCommGroup (H n)] [∀ n,AddCommGroup (C n)]
  [∀ n,Module F (H n)] [∀ n,Module F (C n)]
variable (h₀ : H₀≃ₗ[F]F) (c₀ : C₀≃ₗ[F]F)
variable (hT : ∀ n,H n≃ₗ[F]H₀) (cT : ∀ n,C n≃ₗ[F]C₀)
variable (Ψ : H₀→ₗ[F]C₀)

/-- Literal all-finite v1.1 producer. Its residual input is the
actual affine model data on the two canonically prolonged models,
not per-place postulated finite-image or payment conclusions. -/
def from_original_pair (u v : ℤ) (noncontact : ∀ j,ContactRadical318.forms u v j≠0)
    (D : ∀ w,charts B m HN CN (literalT u v) h₀ c₀ hT cT Ψ w) :
    Output HN CN (literalT u v) (k h₀ c₀ Ψ) :=
  all_finite B m HN CN (literalT u v) h₀ c₀ hT cT Ψ
    (literal_poles_excluded u v noncontact) D

end OriginalLiteralFiveContactAllFinite318
