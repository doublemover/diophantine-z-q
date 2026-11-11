module
public import PELUnlevelledNormalizerAction318
public section
noncomputable section
namespace PELOriginalLevelFiberEquivariance318
open QuaternionicJointPeriodTopology318 PELPositiveOrderNormalizer318 PELPositiveNormalizerMobius318
open PELNormalizerArithmeticBase318 PELPositiveNormalizerNormOne318 PELPositiveNormalizerEffective318
open PELPrincipalThreeCovering318 PELUnlevelledComplexBase318 PELUnlevelledNormalizerAction318
open PELFineLevelFibers318 PELLevelOrbitKernel318 PELEffectivePositiveLevel318
set_option maxHeartbeats 1600000

/-- The actual fine-base normalizer map restricts to the literal fiber
above the transformed original upper-half-plane parameter. -/
@[expose] def fiberTransport (g : positiveNormalizer) (τ : HalfPlane) :
    LevelFiber τ → LevelFiber (baseAction g τ) := fun p =>
  ⟨arithmeticAction g p.val,by
    rw [forgetLevel_equivariant,p.property,coarseAction_square]⟩

/-- Exact equivariance of all18 labels: the same global unit conjugation
and the same original finite reduction determine the transformed fiber point. -/
theorem label_square (g : positiveNormalizer) (τ : HalfPlane) (a : EffectivePositiveLevel) :
    fiberTransport g τ (levelToFiber τ a)=
      levelToFiber (baseAction g τ) (effectiveConjugation g a) := by
  apply Subtype.ext
  change arithmeticAction g (baseQuotient (chosenLift a • τ))=
    baseQuotient (chosenLift (effectiveConjugation g a) • baseAction g τ)
  rw [arithmeticAction_square,base_equivariant]
  apply (orbit_eq_iff _ _ (baseAction g τ)).mpr
  rw [←effective_reduction_square,chosenLift_spec,chosenLift_spec]

/-- A bijection between the ACTUAL fibers, whose comparison with the
already constructed analytic map is proved separately below. -/
@[expose] def fiberEquiv (g : positiveNormalizer) (τ : HalfPlane) :
    LevelFiber τ ≃ LevelFiber (baseAction g τ) :=
  (levelFiberEquiv τ).symm.trans
    ((effectiveConjugation g).toEquiv.trans (levelFiberEquiv (baseAction g τ)))

theorem fiberEquiv_is_actual (g : positiveNormalizer) (τ : HalfPlane) (p : LevelFiber τ) :
    fiberEquiv g τ p=fiberTransport g τ p := by
  obtain ⟨a,rfl⟩ := (levelFiberEquiv τ).surjective p
  change levelToFiber (baseAction g τ)
    (effectiveConjugation g ((levelFiberEquiv τ).symm (levelFiberEquiv τ a)))=
      fiberTransport g τ (levelToFiber τ a)
  rw [Equiv.symm_apply_apply]
  exact (label_square g τ a).symm

theorem fiberTransport_bijective (g : positiveNormalizer) (τ : HalfPlane) :
    Function.Bijective (fiberTransport g τ) := by
  have he : fiberTransport g τ=fiberEquiv g τ := funext (fun p => (fiberEquiv_is_actual g τ p).symm)
  rw [he]
  exact (fiberEquiv g τ).bijective
end PELOriginalLevelFiberEquivariance318
