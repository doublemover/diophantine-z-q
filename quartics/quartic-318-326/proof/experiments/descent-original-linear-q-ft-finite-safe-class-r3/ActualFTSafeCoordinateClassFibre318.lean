module
public import ActualLinearQLiteralSafeNormFibre318
public import ActualFTTwoElementCoefficient318
public section
noncomputable section
namespace ActualFTSafeCoordinateClassFibre318

open scoped BigOperators
open ActualLinearQLiteralSafeNormFibre318

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Uniform finite tag domain at one fresh prime. This does not
depend on which rational norm the eventual affine cell asks for. -/
@[expose] def good (x : F×F) : Prop :=
  x.1^2+x.2^2≠0 ∧ (x.1-1)^2+x.2^2≠0 ∧ (x.1+1)^2+x.2^2≠0

abbrev Tag (F : Type*) [Field F] := {x : F×F // good x}

@[expose] def tagNorm (x : Tag F) : Fˣ :=
  Units.mk0 (x.val.1^2+x.val.2^2) x.prop.1

theorem tagNorm_val (x : Tag F) :
    (tagNorm x:F)=x.val.1^2+x.val.2^2 := by rfl

/-- The class tags compatible with this nonzero norm are exactly
the original safe points. The two avoids are conditions in the same
fibre and the same tag, not independent random events. -/
def fibre (n : F) (hn : n≠0) : {x : Tag F // (tagNorm x:F)=n} ≃ ↥(safe n) where
  toFun x := ⟨x.val.val,(safe_iff n _).mpr ⟨by simpa only [tagNorm_val] using x.prop,x.val.prop.2⟩⟩
  invFun y :=
    let H := (safe_iff n y.val).mp y.prop
    ⟨⟨y.val,⟨(H.1.symm ▸ hn),H.2⟩⟩,by simpa only [tagNorm_val] using H.1⟩
  left_inv x := Subtype.ext (Subtype.ext rfl)
  right_inv y := Subtype.ext rfl

theorem fibre_card (n : F) (hn : n≠0) :
    Nat.card {x : Tag F // (tagNorm x:F)=n}=(safe n).card := by
  rw [Nat.card_congr (fibre n hn),Nat.card_eq_fintype_card,Fintype.card_coe]

/-- Exact normalized compatible-tag lower over the full density
q−χ(−1). It is a finite inequality; no FT application is inferred. -/
theorem compatible_fraction (hF : ringChar F≠2) (h2 : (2:F)≠0) (n : F)
    (hn : n≠0) (hCard : 0 < (normSet n).card) :
    1-4/((normSet n).card:ℝ) ≤
      (Nat.card {x : Tag F // (tagNorm x:F)=n}:ℝ)/((normSet n).card:ℝ) := by
  rw [fibre_card n hn]
  exact safe_fraction_lower hF h2 hn hCard

end ActualFTSafeCoordinateClassFibre318
