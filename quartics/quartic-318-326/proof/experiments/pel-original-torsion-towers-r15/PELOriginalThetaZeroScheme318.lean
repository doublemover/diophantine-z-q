module
public import PrincipalFrameZeroScheme318
public import PELOriginalAlgebraicThetaSection318
public import PELOriginalProperComplexCandidate318
public section
noncomputable section
namespace PELOriginalThetaZeroScheme318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalLevelTheta318
open PELOriginalAllPowerFrameCoordinates318
variable (τ : ℂ) (hτ : 0 < τ.im)

@[expose] def coefficient (a : NonemptyIndex τ hτ) : Γ(candidate τ hτ,opens τ hτ a) :=
  PELOriginalAllPowerMixedCoefficients318.coefficient τ hτ 1 a
    (PELOriginalWholeHZeroDimension318.thetaVector τ hτ 1 (0 : Label 1))
@[expose] def transition (a b : NonemptyIndex τ hτ) : Γ(candidate τ hτ,opens τ hτ a ⊓ opens τ hτ b)ˣ :=
  (LineFrameCocycle318.cocycle (Power τ hτ 1) (opens τ hτ) (frame τ hτ 1)).transition a b
lemma compatible (a b : NonemptyIndex τ hτ) :
    (candidate τ hτ).presheaf.map (homOfLE inf_le_left).op (coefficient τ hτ a)=
      (transition τ hτ a b).val*
        (candidate τ hτ).presheaf.map (homOfLE inf_le_right).op (coefficient τ hτ b) :=
  PELOriginalAllPowerGlobalSections318.transition τ hτ 1 _ a b

/-- The actual scheme-theoretic zero locus of the original theta section
of the SAME algebraic degree-one line. Every local equation is its exact
inverse-frame coefficient; no radical/reduced replacement is made. -/
abbrev zeroScheme : Scheme := PrincipalFrameZeroScheme318.scheme
  (opens τ hτ) (coefficient τ hτ) (transition τ hτ) (compatible τ hτ)
abbrev inclusion : zeroScheme τ hτ ⟶ candidate τ hτ := PrincipalFrameZeroScheme318.inclusion
  (opens τ hτ) (coefficient τ hτ) (transition τ hτ) (compatible τ hτ)
instance closed : IsClosedImmersion (inclusion τ hτ) := PrincipalFrameZeroScheme318.closed
  (opens τ hτ) (coefficient τ hτ) (transition τ hτ) (compatible τ hτ) (coversTop τ hτ)

abbrev localEquation (a : NonemptyIndex τ hτ) : Γ((opens τ hτ a).toScheme,⊤) :=
  PrincipalFrameZeroOverlaps318.coefficient (opens τ hτ) (coefficient τ hτ) a
abbrev localIdeal (a : NonemptyIndex τ hτ) := PrincipalFrameZeroOverlaps318.ideal
  (opens τ hτ) (coefficient τ hτ) a
abbrev localZero (a : NonemptyIndex τ hτ) := (localIdeal τ hτ a).subscheme
abbrev chart (a : NonemptyIndex τ hτ) : localZero τ hτ a ⟶ zeroScheme τ hτ :=
  PrincipalFrameZeroScheme318.chart (opens τ hτ) (coefficient τ hτ)
    (transition τ hτ) (compatible τ hτ) a

/-- Exact full-scheme Cartesian restriction to EVERY original mixed
open, retaining the complete principal ideal and all multiplicities. -/
theorem cartesian (a : NonemptyIndex τ hτ) : IsPullback
    (localIdeal τ hτ a).subschemeι (chart τ hτ a) (opens τ hτ a).ι (inclusion τ hτ) :=
  PrincipalFrameZeroScheme318.cartesian (opens τ hτ) (coefficient τ hτ)
    (transition τ hτ) (compatible τ hτ) a
@[expose] def ideal : (candidate τ hτ).IdealSheafData := (inclusion τ hτ).ker
lemma ideal_restriction (a : NonemptyIndex τ hτ) :
    (ideal τ hτ).comap (opens τ hτ a).ι=localIdeal τ hτ a :=
  PrincipalFrameZeroScheme318.kernel_restriction (opens τ hτ) (coefficient τ hτ)
    (transition τ hτ) (compatible τ hτ) (coversTop τ hτ) a

/-- The local equations are literally coefficients of the already
constructed nonzero global section, through the actual tensor-unit iso. -/
lemma actual_section_coefficient (a : NonemptyIndex τ hτ) :
    PELOriginalAllPowerFrameCoordinates318.coefficient τ hτ 1
      ((PELOriginalAlgebraicThetaSection318.powerOneIso τ hτ).inv.app ⊤
        (PELOriginalAlgebraicThetaSection318.theta τ hτ)) a=coefficient τ hτ a :=
  PELOriginalAlgebraicThetaSection318.theta_coefficient τ hτ a

@[expose] def structureMap : zeroScheme τ hτ ⟶ Spec (CommRingCat.of ℂ) :=
  inclusion τ hτ≫PELOriginalProperComplexCandidate318.structureMap τ hτ
instance proper : IsProper (structureMap τ hτ) := by
  dsimp [structureMap]
  infer_instance
end PELOriginalThetaZeroScheme318
