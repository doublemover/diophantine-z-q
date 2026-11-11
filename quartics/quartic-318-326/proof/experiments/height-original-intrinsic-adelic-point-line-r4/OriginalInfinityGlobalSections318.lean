module
public import OriginalInfinityRatioSections318
public import FourRootRatioPuncturedSections318
public import NormalizedWholeTensorSections318
public section
noncomputable section
namespace OriginalInfinityGlobalSections318
open AlgebraicGeometry CategoryTheory Polynomial
open OriginalInfinityRatioParameters318 FourRootRatioOrder318 FourRootIntegralDuality318
open FiniteDualTransport318
variable (V : Type*) [CommRing V] (d a : Fin 4 → V)
local notation "R" => Base V d a
local notation "q" => common V d a
local notation "r" => ratios V d a
local notation "L" => NormalizedWholeDualitySheaf318.line V d a
local notation "T" => IntrinsicTensorSheaf318.tensor L L

/-- The actual whole reciprocal model dual tensor is scalar-extended and
reparameterized through the same original polynomial equations. -/
@[expose] def integralExtension := FourRootDualParameterBaseChange318.squareMap
  (DVRNormalizedInfinityOrder318.coefficient V d a) (original q r)
  (fun i => (parameter V d a i).symm)

lemma integralExtension_section (p : V[X]) : integralExtension V d a
    (NormalizedDualBicanonicalSections318.infinitySection V d a p)=
      squareFrame (frame (original q r))
        (algebraMap R (OriginalOrder q r) (algebraMap V[X] R p)) :=
  FourRootDualParameterBaseChange318.squareMap_scalar _ _ _ p

/-- Full composite from arbitrary actual GLOBAL intrinsic tensor sections
through original integral whole-order tensors, actual localization and the
proved normalized-order generic equivalence. -/
@[expose] def genericImage (s : Γ(T,⊤)) :=
  squareTransport (FourRootRatioPuncturedSections318.genericEquiv q r)
    (FourRootRatioPuncturedSections318.originalExtension q r
      (integralExtension V d a (NormalizedWholeTensorSections318.infinityTensor V d a s)))

/-- The same global q0 section extends as the explicitly constructed
INTEGRAL ratio-order section c*h^-3*S, with actual full tensor maps. -/
theorem global0_image : genericImage V d a (NormalizedWholeIntrinsicTensor318.section0 V d a)=
    FourRootRatioPuncturedSections318.ratioExtension q r (OriginalInfinityRatioSections318.section0 V d a) := by
  rw [genericImage,NormalizedWholeTensorSections318.section0_infinity,integralExtension_section,
    OriginalInfinityRatioSections318.old_coefficient0]
  exact FourRootRatioPuncturedSections318.section0_comparison q r
    (denominatorUnit V d a) (coordinate V d a) (OriginalInfinityRatioSections318.scalar V d a)
    (common_eq V d a)

/-- The same global q1 section extends as c*h^-3. The actual sixth-power
normalization discrepancy has been discharged, not hidden in a frame label. -/
theorem global1_image : genericImage V d a (NormalizedWholeIntrinsicTensor318.section1 V d a)=
    FourRootRatioPuncturedSections318.ratioExtension q r (OriginalInfinityRatioSections318.section1 V d a) := by
  rw [genericImage,NormalizedWholeTensorSections318.section1_infinity,integralExtension_section,
    OriginalInfinityRatioSections318.old_coefficient1]
  exact FourRootRatioPuncturedSections318.section1_comparison q r
    (denominatorUnit V d a) (coordinate V d a) (OriginalInfinityRatioSections318.scalar V d a)
    (common_eq V d a)
end OriginalInfinityGlobalSections318
