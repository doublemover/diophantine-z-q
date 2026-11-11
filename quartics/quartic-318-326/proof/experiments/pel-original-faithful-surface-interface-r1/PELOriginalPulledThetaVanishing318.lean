module
public import PullbackSectionZero318
public import PELOriginalThetaUniversalVanishing318
public section
noncomputable section
namespace PELOriginalPulledThetaVanishing318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
open PELOriginalAlgebraicPolarizationLine318 PELOriginalAlgebraicThetaSection318
open PELOriginalAllPowerFrameCoordinates318 PELOriginalAllPowerGlobalSections318
variable (τ : ℂ) (hτ : 0 < τ.im) {T : Scheme} (f : T ⟶ candidate τ hτ)

/-- The genuine pullback of the SAME algebraic theta SECTION MORPHISM,
normalized only by the actual canonical pullback-of-unit isomorphism. -/
@[expose] def section : SheafOfModules.unit T.ringCatSheaf ⟶
    (Scheme.Modules.pullback f).obj (sheaf τ hτ) :=
  (IdentityCotangent318.pullbackUnitIso f).inv≫(Scheme.Modules.pullback f).map (thetaMap τ hτ)

lemma morphism_zero_iff : (Scheme.Modules.pullback f).map (thetaMap τ hτ)=0 ↔
    PELOriginalThetaUniversalVanishing318.Vanishing τ hτ f := by
  have hp : (Scheme.Modules.pullback f).map (thetaMap τ hτ)=0 ↔
      (Scheme.Modules.pullback f).map (sectionMap τ hτ 1
        (PELOriginalWholeHZeroDimension318.thetaVector τ hτ 1 0))=0 := by
    rw [thetaMap,Functor.map_comp]
    constructor
    · intro h
      apply (cancel_mono ((Scheme.Modules.pullback f).map (powerOneIso τ hτ).hom)).1
      simpa only [zero_comp] using h
    · intro h; rw [h,zero_comp]
  rw [hp]
  apply PullbackSectionZero318.zero_iff f (Power τ hτ 1) _ (opens τ hτ) (coversTop τ hτ)
    (frame τ hτ 1) (PELOriginalThetaZeroScheme318.coefficient τ hτ)
  intro a W hW
  have h := sectionMap_subopen τ hτ 1
    (PELOriginalWholeHZeroDimension318.thetaVector τ hτ 1 0) a W hW 1
  simpa only [one_mul] using h

/-- Universal vanishing of the ORIGINAL pulled-back theta itself,
including infinitesimal/nonreduced tests, is the coefficient criterion. -/
theorem zero_iff : section τ hτ f=0 ↔ PELOriginalThetaUniversalVanishing318.Vanishing τ hτ f := by
  rw [←morphism_zero_iff]
  constructor
  · intro h
    apply (cancel_epi (IdentityCotangent318.pullbackUnitIso f).inv).1
    simpa only [section,comp_zero] using h
  · intro h; rw [section,h,comp_zero]

/-- The SAME full original theta zero scheme represents vanishing of
the genuine pulled-back global section, not just residue-field tests. -/
theorem existsUnique_lift_iff :
    (∃! g : T ⟶ PELOriginalThetaZeroScheme318.zeroScheme τ hτ,
      g≫PELOriginalThetaZeroScheme318.inclusion τ hτ=f) ↔ section τ hτ f=0 := by
  rw [PELOriginalThetaUniversalVanishing318.existsUnique_lift_iff,zero_iff]

@[expose] def lift (h : section τ hτ f=0) : T ⟶ PELOriginalThetaZeroScheme318.zeroScheme τ hτ :=
  PELOriginalThetaUniversalVanishing318.lift τ hτ f ((zero_iff τ hτ f).mp h)
@[reassoc] lemma lift_inclusion (h : section τ hτ f=0) :
    lift τ hτ f h≫PELOriginalThetaZeroScheme318.inclusion τ hτ=f :=
  PELOriginalThetaUniversalVanishing318.lift_inclusion τ hτ f _
end PELOriginalPulledThetaVanishing318
