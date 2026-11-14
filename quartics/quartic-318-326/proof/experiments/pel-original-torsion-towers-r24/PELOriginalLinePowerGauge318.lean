module
public import PELOriginalMixedPowerTransition318
public import PELOriginalAlgebraicLineCocycle318
public import FramedLineTensorPower318
public import CocycleGaugeIso318
public section
noncomputable section
namespace PELOriginalLinePowerGauge318
open AlgebraicGeometry CategoryTheory Opposite
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicPolarizationLine318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The actual degree-six comparison unit in the ORIGINAL open ring. -/
@[expose] def gauge (a : NonemptyIndex τ hτ) : Γ(candidate τ hτ,opens τ hτ a)ˣ :=
  Units.map (LineFrameTopScalar318.ringTop (opens τ hτ a)).hom.hom.toMonoidHom
    (PELOriginalMixedPowerUnit318.unit τ hτ a.val)

lemma gauge_restrict (a : NonemptyIndex τ hτ) (W : (candidate τ hτ).Opens)
    (h : W ≤ opens τ hτ a) :
    (LineFrameTopScalar318.ringTop W).inv
      ((candidate τ hτ).presheaf.map (homOfLE h).op (gauge τ hτ a).val) =
      ((candidate τ hτ).homOfLE h).appTop (PELOriginalMixedPowerUnit318.value τ hτ a.val) := by
  simp only [gauge,Units.coe_map,PELOriginalMixedPowerUnit318.unit_value]
  exact OriginalOpenCoefficientSpecialization318.coefficient_pullback _ _ _ _

abbrev cubicCocycle := LineFrameCocycle318.cocycle (cubicSheaf τ hτ) (opens τ hτ) (cubicFrame τ hτ)
abbrev quadraticCocycle := LineFrameCocycle318.cocycle (quadraticSheaf τ hτ) (opens τ hτ) (quadraticFrame τ hτ)

/-- Equality of actual ORIGINAL overlap-ring units for the two sixth
power presentations. No complex point remains in this equation. -/
theorem power_equation (a b : NonemptyIndex τ hτ) :
    Units.map ((candidate τ hτ).presheaf.map (homOfLE inf_le_right).op).hom.toMonoidHom (gauge τ hτ b) *
      ((cubicCocycle τ hτ).transition a b)^2 =
    Units.map ((candidate τ hτ).presheaf.map (homOfLE inf_le_left).op).hom.toMonoidHom (gauge τ hτ a) *
      ((quadraticCocycle τ hτ).transition a b)^3 := by
  apply Units.ext
  apply (LineFrameTopScalar318.ringTop (opens τ hτ a ⊓ opens τ hτ b)).inv.injective
  simp only [Units.val_mul,Units.val_pow_eq_pow_val,Units.coe_map,map_mul,map_pow]
  rw [gauge_restrict,gauge_restrict,
    PELOriginalAlgebraicLineCocycle318.cubic_transition_pullback,
    PELOriginalAlgebraicLineCocycle318.quadratic_transition_pullback]
  exact PELOriginalMixedPowerTransition318.power_transition τ hτ a.val b.val

/-- The cubic-square cocycle is the literal coboundary of the produced
regular units times the quadratic-cube cocycle. -/
theorem gauge_equation (a b : NonemptyIndex τ hτ) :
    (UnitCocyclePower318.power (cubicCocycle τ hτ) 2).transition a b =
      UnitTransitionCocycle318.coboundary (StructureUnitsSheaf318.units (candidate τ hτ)).obj
        (opens τ hτ) (gauge τ hτ) a b *
      (UnitCocyclePower318.power (quadraticCocycle τ hτ) 3).transition a b := by
  let l := Units.map ((candidate τ hτ).presheaf.map (homOfLE inf_le_left).op).hom.toMonoidHom
    (gauge τ hτ a)
  let r := Units.map ((candidate τ hτ).presheaf.map (homOfLE inf_le_right).op).hom.toMonoidHom
    (gauge τ hτ b)
  have h : r*((cubicCocycle τ hτ).transition a b)^2 =
      l*((quadraticCocycle τ hτ).transition a b)^3 := power_equation τ hτ a b
  change ((cubicCocycle τ hτ).transition a b)^2 =
    (l*r⁻¹)*((quadraticCocycle τ hτ).transition a b)^3
  calc
    _ = r⁻¹*(r*((cubicCocycle τ hτ).transition a b)^2) := by simp
    _ = r⁻¹*(l*((quadraticCocycle τ hτ).transition a b)^3) := by rw [h]
    _ = _ := by ac_rfl

/-- A genuine isomorphism of the actual sheafified tensor powers:
quadratic cubed equals cubic squared. Both inverse maps come from the
produced gauge isomorphism and exact frame reconstruction. -/
@[expose] def sixthPowerIso :
    FramedLineTensorPower318.object (quadraticSheaf τ hτ) 3 ≅
      FramedLineTensorPower318.object (cubicSheaf τ hτ) 2 :=
  FramedLineTensorPower318.iso (quadraticSheaf τ hτ) (opens τ hτ)
    (quadraticFrame τ hτ) (coversTop τ hτ) 3 ≪≫
  CocycleGaugeIso318.iso (opens τ hτ)
    (UnitCocyclePower318.power (quadraticCocycle τ hτ) 3)
    (UnitCocyclePower318.power (cubicCocycle τ hτ) 2)
    (gauge τ hτ) (gauge_equation τ hτ) ≪≫
  (FramedLineTensorPower318.iso (cubicSheaf τ hτ) (opens τ hτ)
    (cubicFrame τ hτ) (coversTop τ hτ) 2).symm

lemma sixthPower_hom_inv : (sixthPowerIso τ hτ).hom ≫ (sixthPowerIso τ hτ).inv = 𝟙 _ :=
  (sixthPowerIso τ hτ).hom_inv_id
lemma sixthPower_inv_hom : (sixthPowerIso τ hτ).inv ≫ (sixthPowerIso τ hτ).hom = 𝟙 _ :=
  (sixthPowerIso τ hτ).inv_hom_id
end PELOriginalLinePowerGauge318
