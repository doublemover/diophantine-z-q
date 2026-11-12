module
public import ActualTwoDescentFieldScalarConnectingHom318
public section
noncomputable section
namespace ActualTwoDescentFieldScalarConnectingKernel318
set_option maxHeartbeats 16000000
variable {F : Type} [Field F] [CharZero F] [DecidableEq F]
local notation "Qbar" => AlgebraicClosure F
local notation "GalQ" => Field.absoluteGaloisGroup F

open ActualTwoDescentFieldAlgebraicClosureHalving318 ActualTwoDescentFieldSquareOneUnits318
open ActualTwoDescentFieldScalarSquareRoots318 ActualTwoDescentFieldScalarRootCharacters318
open ActualTwoDescentFieldScalarRootIndependence318 ActualTwoDescentFieldScalarConnectingHom318
open ActualTwoDescentFieldGaloisFixedRational318

lemma actual_scalar_connecting_one (a : Fˣ) :
    (scalarConnectingHom (F:=F)) a=1 ↔ ∃ b : Fˣ, b^2=a := by
  constructor
  · intro H
    have hfix (σ : GalQ) : σ (scalarRoot a)=scalarRoot a := by
      have h := congrArg (fun f : (continuousCharacters (F:=F)) => (((f : GalQ →* SquareOne Qbar) σ : Qbarˣ) : Qbar)) H
      change σ (scalarRoot a)/scalarRoot a=1 at h
      simpa only [one_mul] using (div_eq_iff (scalar_root_ne a)).mp h
    obtain ⟨b,hb⟩ := actual_fixed_coordinate_rational _ hfix
    have hbn : b ≠ 0 := by intro he; subst b; rw [map_zero] at hb; exact scalar_root_ne a hb.symm
    refine ⟨Units.mk0 b hbn,?_⟩
    apply Units.ext
    apply (algebraMap F Qbar).injective
    change algebraMap F Qbar (b^2)=algebraMap F Qbar (a : F)
    rw [map_pow,hb,scalar_root_square]
  · rintro ⟨b,rfl⟩
    apply Subtype.ext
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    apply Units.ext
    change ((scalarCharacter (b^2) σ : Qbarˣ) : Qbar)=1
    rw [actual_scalar_character_evaluate (b^2) (algebraMap F Qbar (b : F))
      (rational_parameter_ne _ b.ne_zero) (by simp only [Units.val_pow_eq_pow_val,map_pow]) σ]
    rw [σ.commutes,div_self (rational_parameter_ne _ b.ne_zero)]

lemma actual_scalar_connecting_kernel : (scalarConnectingHom (F:=F)).ker=(powMonoidHom (α:=Fˣ) 2).range := by
  ext a
  exact actual_scalar_connecting_one a

end ActualTwoDescentFieldScalarConnectingKernel318
