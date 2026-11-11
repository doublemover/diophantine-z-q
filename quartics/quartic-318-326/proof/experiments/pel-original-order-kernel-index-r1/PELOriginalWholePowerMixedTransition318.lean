module
public import PELOriginalWholePowerMixedCoefficient318
public import PELOriginalAlgebraicLineCocycle318
public import FramedLineTensorPower318
public section
noncomputable section
namespace PELOriginalWholePowerMixedTransition318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalMixedRatioCover318 PELOriginalMixedPointEvaluation318
open PELOriginalSectionMultiplication318 PELOriginalWholePowerMixedCoefficient318
open PELOriginalAlgebraicPolarizationLine318
variable (τ : ℂ) (hτ : 0 < τ.im) (m : ℕ)
local instance candidateReduced : IsReduced (candidate τ hτ) := reduced τ hτ

/-- The regular coefficients satisfy the actual mth-power cubic
transition on the ENTIRE mixed overlap. -/
theorem transition (a b : Index) (s : homogeneous τ hτ (3*m)) :
    (toLeft τ hτ a b).appTop (coefficient τ hτ m a s)=
      (toRight τ hτ a b).appTop (coefficient τ hτ m b s) *
        ((toLeft τ hτ a b).appTop (cubic τ hτ a b.1))^m := by
  let π := (overlap τ hτ a b).ι ≫ PELOriginalProperComplexCandidate318.structureMap τ hτ
  letI : LocallyOfFiniteType π := by dsimp [π]; infer_instance
  apply ReducedSchemeGlobalFunctionSeparation318.ext π
  intro p hp
  let pL := p ≫ toLeft τ hτ a b
  let pR := p ≫ toRight τ hτ a b
  have hL : pL ≫ (mixedOpen τ hτ a).ι ≫
      PELOriginalProperComplexCandidate318.structureMap τ hτ=𝟙 _ := by
    simpa only [pL,toLeft,Category.assoc,Scheme.homOfLE_ι_assoc] using hp
  obtain ⟨z,h3a,h2a,hA,heL⟩ := point_representation τ hτ a pL hL
  have heR : pR ≫ (mixedOpen τ hτ b).ι = candidateComplexPoint τ hτ (projection (P τ) z) := by
    simpa only [pR,pL,toRight,toLeft,Category.assoc,Scheme.homOfLE_ι] using heL
  obtain ⟨h3b,h2b⟩ := coordinates_nonzero τ hτ b pR z heR
  apply (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.injective
  simp only [map_mul,map_pow]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (pL.appTop (coefficient τ hτ m a s)) =
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
      (pR.appTop (coefficient τ hτ m b s)) *
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (pL.appTop (cubic τ hτ a b.1)))^m
  rw [evaluation τ hτ m a s pL z h3a heL,evaluation τ hτ m b s pR z h3b heR,
    cubic_evaluation τ hτ a b.1 pL hL z h3a heL]
  simp only [PELOriginalWholePowerRatioCover318.coverRatio]
  field_simp [h3a,h3b]

/-- Coefficients as sections of the original ambient sheaf, not only
as functions on the open subscheme. -/
@[expose] def originalCoefficient (a : NonemptyIndex τ hτ) (s : homogeneous τ hτ (3*m)) :
    Γ(candidate τ hτ,opens τ hτ a) :=
  (LineFrameTopScalar318.ringTop (opens τ hτ a)).hom (coefficient τ hτ m a.val s)

/-- Exact compatibility with the EXTRACTED cocycle of the actual
iterated tensor sheaf. This includes degree zero without a special cover. -/
theorem original_transition (a b : NonemptyIndex τ hτ) (s : homogeneous τ hτ (3*m)) :
    (candidate τ hτ).presheaf.map (homOfLE
      (show opens τ hτ a ⊓ opens τ hτ b ≤ opens τ hτ a from inf_le_left)).op
        (originalCoefficient τ hτ m a s) =
    ((LineFrameCocycle318.cocycle
      (FramedLineTensorPower318.object (cubicSheaf τ hτ) m) (opens τ hτ)
      (FramedLineTensorPower318.frames (cubicSheaf τ hτ) (opens τ hτ)
        (cubicFrame τ hτ) m)).transition a b).val *
    (candidate τ hτ).presheaf.map (homOfLE
      (show opens τ hτ a ⊓ opens τ hτ b ≤ opens τ hτ b from inf_le_right)).op
        (originalCoefficient τ hτ m b s) := by
  rw [FramedLineTensorPower318.transition,Units.val_pow_eq_pow_val]
  apply (LineFrameTopScalar318.ringTop (opens τ hτ a ⊓ opens τ hτ b)).inv.injective
  rw [map_mul,map_pow,PELOriginalAlgebraicLineCocycle318.cubic_transition_pullback]
  change (LineFrameTopScalar318.ringTop (opens τ hτ a ⊓ opens τ hτ b)).inv
      (GlobalSectionFrameCoordinates318.coefficient (opens τ hτ a)
        (coefficient τ hτ m a.val s) _ inf_le_left) =
    ((toLeft τ hτ a.val b.val).appTop (cubic τ hτ a.val b.val.1))^m *
    (LineFrameTopScalar318.ringTop (opens τ hτ a ⊓ opens τ hτ b)).inv
      (GlobalSectionFrameCoordinates318.coefficient (opens τ hτ b)
        (coefficient τ hτ m b.val s) _ inf_le_right)
  rw [OriginalOpenCoefficientSpecialization318.coefficient_pullback,
    OriginalOpenCoefficientSpecialization318.coefficient_pullback]
  simpa only [mul_comm] using transition τ hτ m a.val b.val s
end PELOriginalWholePowerMixedTransition318
