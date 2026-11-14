module
public import ActualPointedKernelMaps318
public section
noncomputable section
namespace OriginalFiveKernelCoordinates318
open AlgebraicGeometry CategoryTheory
open ContactRelativeLinePresheaf318 SourceTwistArithmetic318
open ActualFiveHOneDecomposition318 ActualSourceHOnePullbacks318
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
abbrev SourceKernel := ActualPointedKernelMaps318.Kernel sourceStructure
abbrev TargetKernel : Index → Type
  | none => ActualPointedKernelMaps318.Kernel fifthStructure
  | some i => ActualPointedKernelMaps318.Kernel (characterStructure i)
instance targetGroup (i : Index) : CommGroup (TargetKernel i) := by
  cases i <;> exact inferInstance
local instance sourceIntegral : IsIntegral ActualSourceHOnePresentation318.Source :=
  ContactProjectiveModel318.model_integral units
local instance sourceProper : IsProper sourceStructure :=
  (ContactGlobalProper318.proper_integral_extension units).2.2
@[expose] def source : Multiplicative SourceHOne ≃* SourceKernel :=
  OriginalHOneKernelGroupEquivalence318.equivalence sourceStructure
    ActualSourceHOnePresentation318.finiteOpen ActualSourceHOnePresentation318.infinityOpen
    ActualSourceHOnePresentation318.finite_affine ActualSourceHOnePresentation318.infinity_affine
    (OriginalFivePointedClassification318.affine_overlap sourceStructure
      ActualSourceHOnePresentation318.finite_affine ActualSourceHOnePresentation318.infinity_affine)
    ActualSourceHOnePresentation318.cover
lemma source_pointed (z : SourceHOne) : source (Multiplicative.ofAdd z) =
    ActualPointedKernelMaps318.pointedEquivalence sourceStructure (OriginalFivePointedClassification318.source z) := rfl
variable (A B : ℚ) [IsIntegral (WeierstrassGluing318.scheme A B)]
@[expose] def weierstrass : Multiplicative (SheafCohomologyRetraction318.structureH (WeierstrassGluing318.scheme A B) 1) ≃*
    ActualPointedKernelMaps318.Kernel (WeierstrassGluing318.structureMap A B) := by
  letI := CubicClosedImmersion318.structure_separated A B
  exact OriginalHOneKernelGroupEquivalence318.equivalence (WeierstrassGluing318.structureMap A B)
    (OriginalHOnePointedMaps318.finiteOpen A B) (OriginalHOnePointedMaps318.infinityOpen A B)
    (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B))
    (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B))
    (OriginalFivePointedClassification318.affine_overlap (WeierstrassGluing318.structureMap A B)
      (isAffineOpen_opensRange (WeierstrassGluing318.finiteChart A B))
      (isAffineOpen_opensRange (WeierstrassGluing318.infinityChart A B)))
    (OriginalHOnePointedMaps318.target_cover A B)
local instance characterIntegral (i : Fin 4) : IsIntegral (CompletedCharacterSchemeMaps318.Target i) :=
  (CompletedCharacterProper318.target_proper_integral i).2
local instance fifthIntegral : IsIntegral FifthCompletedGlobal318.Target := FifthCompletedProper318.target_proper_integral.2
@[expose] def target : (i : Index) → Multiplicative (TargetHOne i) ≃* TargetKernel i
  | none => weierstrass FifthCharacterShortPolynomial318.A FifthCharacterShortPolynomial318.B
  | some i => weierstrass (publishedA i) (publishedB i)
@[expose] def targetPointed : (i : Index) → OriginalFivePointedNorms318.TargetClass i ≃ TargetKernel i
  | none => ActualPointedKernelMaps318.pointedEquivalence fifthStructure
  | some i => ActualPointedKernelMaps318.pointedEquivalence (characterStructure i)
lemma target_pointed (i : Index) (z : TargetHOne i) :
    target i (Multiplicative.ofAdd z) = targetPointed i (OriginalFivePointedNorms318.classification i z) := by
  cases i <;> rfl
/-- The SAME actual five kernel pullbacks, restricted from original line-class
pullbacks, not defined by conjugating H1 maps. -/
@[expose] def pullback : (i : Index) → TargetKernel i →* SourceKernel
  | none => ActualPointedKernelMaps318.pullback sourceStructure fifthStructure
      FifthCompletedGlobal318.map FifthCompletedGlobal318.over_Q
  | some i => ActualPointedKernelMaps318.pullback sourceStructure (characterStructure i)
      (CompletedCharacterGlobal318.completedMap i) (CompletedCharacterGlobal318.over_Q i)
lemma pullback_pointed (i : Index) (L : OriginalFivePointedNorms318.TargetClass i) :
    pullback i (targetPointed i L) = ActualPointedKernelMaps318.pointedEquivalence sourceStructure
      (OriginalFivePointedNorms318.pullback i L) := by
  cases i with
  | none => exact ActualPointedKernelMaps318.pointed_pullback _ _ _ _ L
  | some j => exact ActualPointedKernelMaps318.pointed_pullback _ _ _ _ L
lemma pullback_target (i : Index) (z : TargetHOne i) :
    pullback i (target i (Multiplicative.ofAdd z)) =
      source (Multiplicative.ofAdd (ActualFiveHOneDecomposition318.pullback i z)) := by
  rw [target_pointed,pullback_pointed,OriginalFivePointedNorms318.pullback_classification,source_pointed]
/-- The genuine pointed determinant norm, forgotten into the ORIGINAL tensor
kernel, not an artificial linear transfer on a renamed carrier. -/
@[expose] def norm (i : Index) (L : SourceKernel) : TargetKernel i :=
  targetPointed i (OriginalFivePointedNorms318.norm i
    ((ActualPointedKernelMaps318.pointedEquivalence sourceStructure).symm L))
lemma norm_source (i : Index) (z : SourceHOne) : norm i (source (Multiplicative.ofAdd z)) =
    target i (Multiplicative.ofAdd (OriginalHOneTraceNormalization318.originalTrace i z)) := by
  rw [source_pointed]
  dsimp only [norm]
  rw [Equiv.symm_apply_apply,OriginalFivePointedNorms318.norm_classification,target_pointed]
end OriginalFiveKernelCoordinates318
