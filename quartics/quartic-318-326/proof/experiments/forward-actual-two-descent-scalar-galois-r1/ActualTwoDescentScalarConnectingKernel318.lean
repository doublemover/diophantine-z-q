module
public import ActualTwoDescentScalarConnectingHom318
public section
noncomputable section
namespace ActualTwoDescentScalarConnectingKernel318
set_option maxHeartbeats 16000000

open ActualTwoDescentAlgebraicClosureHalving318 ActualTwoDescentSquareOneUnits318
open ActualTwoDescentScalarSquareRoots318 ActualTwoDescentScalarRootCharacters318
open ActualTwoDescentScalarRootIndependence318 ActualTwoDescentScalarConnectingHom318
open ActualTwoDescentGaloisFixedRational318

lemma actual_scalar_connecting_one (a : ℚˣ) :
    scalarConnectingHom a=1 ↔ ∃ b : ℚˣ, b^2=a := by
  constructor
  · intro H
    have hfix (σ : GalQ) : σ (scalarRoot a)=scalarRoot a := by
      have h := congrArg (fun f : continuousCharacters => (((f : GalQ →* SquareOne Qbar) σ : Qbarˣ) : Qbar)) H
      change σ (scalarRoot a)/scalarRoot a=1 at h
      simpa only [one_mul] using (div_eq_iff (scalar_root_ne a)).mp h
    obtain ⟨b,hb⟩ := actual_fixed_coordinate_rational _ hfix
    have hbn : b ≠ 0 := by intro he; subst b; rw [map_zero] at hb; exact scalar_root_ne a hb.symm
    refine ⟨Units.mk0 b hbn,?_⟩
    apply Units.ext
    apply (algebraMap ℚ Qbar).injective
    change algebraMap ℚ Qbar (b^2)=algebraMap ℚ Qbar (a : ℚ)
    rw [map_pow,hb,scalar_root_square]
  · rintro ⟨b,rfl⟩
    apply Subtype.ext
    apply MonoidHom.ext
    intro σ
    apply Subtype.ext
    apply Units.ext
    change ((scalarCharacter (b^2) σ : Qbarˣ) : Qbar)=1
    rw [actual_scalar_character_evaluate (b^2) (algebraMap ℚ Qbar (b : ℚ))
      (rational_parameter_ne _ b.ne_zero) (by simp only [Units.val_pow_eq_pow_val,map_pow]) σ]
    rw [σ.commutes,div_self (rational_parameter_ne _ b.ne_zero)]

lemma actual_scalar_connecting_kernel : scalarConnectingHom.ker=(powMonoidHom (α:=ℚˣ) 2).range := by
  ext a
  exact actual_scalar_connecting_one a

end ActualTwoDescentScalarConnectingKernel318
