module
public import ActualTwoDescentFieldScalarRootCharacters318
public section
noncomputable section
namespace ActualTwoDescentFieldScalarRootIndependence318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentFieldAlgebraicClosureHalving318 ActualTwoDescentFieldSquareOneUnits318
open ActualTwoDescentFieldScalarSquareRoots318 ActualTwoDescentFieldScalarRootCharacters318

lemma actual_same_root_ratio (a : Fˣ) (r s : Qbar) (hr : r ≠ 0) (hss : s ≠ 0)
    (hR : r^2=algebraMap F Qbar (a : F)) (hS : s^2=algebraMap F Qbar (a : F)) (σ : GalQ) :
    σ r/r=σ s/s := by
  let u : SquareOne Qbar := ⟨Units.mk0 (r/s) (div_ne_zero hr hss),by
    apply Units.ext
    change (r/s)^2=1
    rw [div_pow,hR,hS,div_self (rational_parameter_ne _ a.ne_zero)]⟩
  have hfix := actual_square_one_aut_fixed σ u
  change σ (r/s)=r/s at hfix
  rw [map_div] at hfix
  have hσs : σ s ≠ 0 := ActualTwoDescentSquareClassFieldMap318.field_map_ne_zero σ.toRingHom hss
  field_simp [hr,hss,hσs] at hfix ⊢
  <;> linear_combination hfix

lemma actual_scalar_character_evaluate (a : Fˣ) (r : Qbar) (hr : r ≠ 0)
    (hs : r^2=algebraMap F Qbar (a : F)) (σ : GalQ) :
    ((scalarCharacter a σ : Qbarˣ) : Qbar)=σ r/r :=
  actual_same_root_ratio a _ r (scalar_root_ne a) hr (scalar_root_square a) hs σ

lemma actual_scalar_character_mul (a b : Fˣ) : scalarCharacter (a*b)=scalarCharacter a*scalarCharacter b := by
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  apply Units.ext
  change ((scalarCharacter (a*b) σ : Qbarˣ) : Qbar)=
    ((scalarCharacter a σ : Qbarˣ) : Qbar)*((scalarCharacter b σ : Qbarˣ) : Qbar)
  have hsq : (scalarRoot a*scalarRoot b)^2=algebraMap F Qbar ((a*b : Fˣ) : F) := by
    rw [mul_pow,scalar_root_square,scalar_root_square,Units.val_mul,map_mul]
  rw [actual_scalar_character_evaluate (a*b) (scalarRoot a*scalarRoot b)
    (mul_ne_zero (scalar_root_ne a) (scalar_root_ne b)) hsq σ]
  change σ (scalarRoot a*scalarRoot b)/(scalarRoot a*scalarRoot b)=
    (σ (scalarRoot a)/scalarRoot a)*(σ (scalarRoot b)/scalarRoot b)
  rw [map_mul,mul_div_mul_comm]

end ActualTwoDescentFieldScalarRootIndependence318
