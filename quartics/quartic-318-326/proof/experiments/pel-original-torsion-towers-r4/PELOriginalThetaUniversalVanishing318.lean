module
public import FramedZeroArbitraryBaseChange318
public import PELOriginalThetaZeroScheme318
public section
noncomputable section
namespace PELOriginalThetaUniversalVanishing318
open AlgebraicGeometry CategoryTheory
open PELOriginalReducedProjectiveCandidate318 PELOriginalMixedRatioCover318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The actual theta coefficients and full unit transition on the
original mixed cover, not a separately postulated vanishing model. -/
@[expose] def data : FramedZeroUniversalData318.Data (candidate τ hτ) where
  Index := NonemptyIndex τ hτ
  opens := opens τ hτ
  coefficient := PELOriginalThetaZeroScheme318.coefficient τ hτ
  transition := PELOriginalThetaZeroScheme318.transition τ hτ
  compatible := PELOriginalThetaZeroScheme318.compatible τ hτ
  covers := coversTop τ hτ
lemma zero_eq : (data τ hτ).Zero=PELOriginalThetaZeroScheme318.zeroScheme τ hτ := rfl
lemma inclusion_eq : (data τ hτ).inclusion=PELOriginalThetaZeroScheme318.inclusion τ hτ := rfl

/-- Literal vanishing in the FULL pulled-back section rings of T. In
particular the condition remembers infinitesimal and nilpotent tests. -/
abbrev Vanishing {T : Scheme} (f : T ⟶ candidate τ hτ) :=
  ∀ a : NonemptyIndex τ hτ,
    f.app (opens τ hτ a) (PELOriginalThetaZeroScheme318.coefficient τ hτ a)=0

theorem existsUnique_lift_iff {T : Scheme} (f : T ⟶ candidate τ hτ) :
    (∃! g : T ⟶ PELOriginalThetaZeroScheme318.zeroScheme τ hτ,
      g≫PELOriginalThetaZeroScheme318.inclusion τ hτ=f) ↔ Vanishing τ hτ f :=
  FramedZeroUniversalLift318.existsUnique_lift_iff (data τ hτ) f
@[expose] def lift {T : Scheme} (f : T ⟶ candidate τ hτ) (h : Vanishing τ hτ f) :
    T ⟶ PELOriginalThetaZeroScheme318.zeroScheme τ hτ :=
  FramedZeroUniversalLift318.lift (data τ hτ) f h
@[reassoc] lemma lift_inclusion {T : Scheme} (f : T ⟶ candidate τ hτ) (h : Vanishing τ hτ f) :
    lift τ hτ f h≫PELOriginalThetaZeroScheme318.inclusion τ hτ=f :=
  FramedZeroUniversalLift318.lift_inclusion (data τ hτ) f h

/-- BOTH inverses for the actual original theta zero scheme on every
scheme test. This is stronger than its already proved C-point support. -/
@[expose] def equivalence (T : Scheme) :
    (T ⟶ PELOriginalThetaZeroScheme318.zeroScheme τ hτ) ≃
      {f : T ⟶ candidate τ hτ // Vanishing τ hτ f} :=
  FramedZeroVanishingEquivalence318.equivalence (data τ hτ) T
lemma naturality {S T : Scheme} (a : S ⟶ T)
    (g : T ⟶ PELOriginalThetaZeroScheme318.zeroScheme τ hτ) :
    (equivalence τ hτ S (a≫g)).val=a≫(equivalence τ hτ T g).val :=
  Category.assoc _ _ _

/-- The literal original global theta section supplies every coefficient
in this universal criterion through its genuine inverse local frame. -/
lemma section_coefficient (a : NonemptyIndex τ hτ) :
    PELOriginalAllPowerFrameCoordinates318.coefficient τ hτ 1
      ((PELOriginalAlgebraicThetaSection318.powerOneIso τ hτ).inv.app ⊤
        (PELOriginalAlgebraicThetaSection318.theta τ hτ)) a=
      (data τ hτ).coefficient a :=
  PELOriginalThetaZeroScheme318.actual_section_coefficient τ hτ a
end PELOriginalThetaUniversalVanishing318
