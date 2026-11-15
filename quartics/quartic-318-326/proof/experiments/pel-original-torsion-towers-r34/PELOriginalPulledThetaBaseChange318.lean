module
public import PELOriginalPulledThetaVanishing318
public import PELOriginalThetaArbitraryBaseChange318
public section
noncomputable section
namespace PELOriginalPulledThetaBaseChange318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318
variable (τ : ℂ) (hτ : 0 < τ.im) {T : Scheme} (f : T ⟶ candidate τ hτ)

/-- Arbitrary base change of the SAME full theta zero scheme represents
vanishing of the actual composite pullback theta section. No flatness,
reducedness, field-valued or finite-type restriction is imposed. -/
theorem existsUnique_lift_iff {S : Scheme} (g : S ⟶ T) :
    (∃! p : S ⟶ PELOriginalThetaArbitraryBaseChange318.zeroScheme τ hτ f,
      p≫PELOriginalThetaArbitraryBaseChange318.inclusion τ hτ f=g) ↔
      PELOriginalPulledThetaVanishing318.section τ hτ (g≫f)=0 := by
  rw [PELOriginalThetaArbitraryBaseChange318.existsUnique_lift_iff,
    PELOriginalPulledThetaVanishing318.zero_iff]

/-- On the ORIGINAL full zero scheme, its actual pulled-back theta is
zero as a module-sheaf morphism, including every infinitesimal direction. -/
lemma original_zero : PELOriginalPulledThetaVanishing318.section τ hτ
    (PELOriginalThetaZeroScheme318.inclusion τ hτ)=0 := by
  apply (PELOriginalPulledThetaVanishing318.existsUnique_lift_iff τ hτ _).mp
  refine ⟨𝟙 _,Category.id_comp _,?_⟩
  intro p hp
  apply (cancel_mono (PELOriginalThetaZeroScheme318.inclusion τ hτ)).1
  simpa only [Category.id_comp] using hp
end PELOriginalPulledThetaBaseChange318
