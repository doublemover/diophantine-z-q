module
public import PELOriginalThetaUniversalVanishing318
public section
noncomputable section
namespace PELOriginalThetaArbitraryBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open PELOriginalReducedProjectiveCandidate318 PELOriginalThetaUniversalVanishing318
variable (τ : ℂ) (hτ : 0 < τ.im) {T : Scheme} (f : T ⟶ candidate τ hτ)

/-- The genuine categorical pullback of the original theta zero scheme. -/
abbrev zeroScheme := pullback f (PELOriginalThetaZeroScheme318.inclusion τ hτ)
abbrev inclusion : zeroScheme τ hτ f ⟶ T := pullback.fst _ _
abbrev toOriginal : zeroScheme τ hτ f ⟶ PELOriginalThetaZeroScheme318.zeroScheme τ hτ :=
  pullback.snd _ _
instance closed : IsClosedImmersion (inclusion τ hτ f) := inferInstance
lemma cartesian : IsPullback (inclusion τ hτ f) (toOriginal τ hτ f)
    f (PELOriginalThetaZeroScheme318.inclusion τ hτ) := IsPullback.of_hasPullback _ _

/-- Full ideal equality for arbitrary base change, with no reduction,
flatness or finite-type hypothesis. Regularity after nonflat pullback is
not inferred from this equality. -/
theorem kernel : (inclusion τ hτ f).ker=(PELOriginalThetaZeroScheme318.ideal τ hτ).comap f :=
  FramedZeroArbitraryBaseChange318.kernel (data τ hτ) f

theorem existsUnique_lift_iff {S : Scheme} (g : S ⟶ T) :
    (∃! p : S ⟶ zeroScheme τ hτ f,p≫inclusion τ hτ f=g) ↔
      Vanishing τ hτ (g≫f) :=
  FramedZeroArbitraryBaseChange318.existsUnique_lift_iff (data τ hτ) f g
@[expose] def lift {S : Scheme} (g : S ⟶ T) (h : Vanishing τ hτ (g≫f)) :
    S ⟶ zeroScheme τ hτ f := FramedZeroArbitraryBaseChange318.lift (data τ hτ) f g h
@[reassoc] lemma lift_inclusion {S : Scheme} (g : S ⟶ T) (h : Vanishing τ hτ (g≫f)) :
    lift τ hτ f g h≫inclusion τ hτ f=g :=
  FramedZeroArbitraryBaseChange318.lift_inclusion (data τ hτ) f g h
end PELOriginalThetaArbitraryBaseChange318
