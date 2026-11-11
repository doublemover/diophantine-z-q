module
public import NormalizedDualBicanonicalSections318
public import FourRootTraceDualLattice318
public import OriginalAllPlaceNormalizedData318
public section
noncomputable section
namespace OriginalAllPrimeFiniteDuality318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
open NormalizedWholeOverlap318 NormalizedDualBicanonicalSections318
open NormalizedWholeDualityFrames318
set_option maxHeartbeats 1600000
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t)) (D : Data c t w)
local notation "R" => V c t w
local notation "d" => D.coefficients
local notation "a" => IntegralSourceBranches318.contacts R

/-- Actual full finite and infinity dual modules on the already produced
original all-place model, including dyadic places and collisions. -/
@[expose] def finiteFrame := NormalizedWholeDualityFrames318.finiteFrame R d a
@[expose] def infinityFrame := NormalizedWholeDualityFrames318.infinityFrame R d a

/-- Both original candidate bicanonical sections are given integrally on
both whole orders, and their genuine tensor images agree on the existing
whole Laurent overlap. No extra excluded-place generators are assumed. -/
theorem section_compatibility :
    (NormalizedCanonicalTensorTransition318.canonicalSquare R d a
      (finiteExtension R d a (section0Finite R d a))=
      infinityExtension R d a (section0Infinity R d a)) ∧
    (NormalizedCanonicalTensorTransition318.canonicalSquare R d a
      (finiteExtension R d a (section1Finite R d a))=
      infinityExtension R d a (section1Infinity R d a)) :=
  ⟨section0_overlap R d a,section1_overlap R d a⟩

/-- The original-model coefficient twists are nonzero, but need not be
units in the valuation ring. This distinction is retained at every place. -/
theorem coefficient_ne (i : Fin 4) : D.coefficients i≠0 := by
  change (D.unit i:R)*D.pi^(D.exponent i:ℕ)≠0
  exact mul_ne_zero (D.unit i).ne_zero (pow_ne_zero _ D.irreducible.ne_zero)

/-- Actual trace formula on the full finite order, before passing to any
local smooth zoom or to a regular resolution. -/
theorem finite_trace (x : FiniteOrder R d a) :
    Algebra.trace R[X] (FiniteOrder R d a) x=
      FourRootIntegralDuality318.coefficient (DVRNormalizedFiniteOrder318.coefficient R d a)
        (((16:R[X]) • FourRootTraceCoefficient318.rootProduct
          (DVRNormalizedFiniteOrder318.coefficient R d a))*x) :=
  FourRootTraceCoefficient318.trace_eq _ x

theorem infinity_trace (x : InfinityOrder R d a) :
    Algebra.trace R[X] (InfinityOrder R d a) x=
      FourRootIntegralDuality318.coefficient (DVRNormalizedInfinityOrder318.coefficient R d a)
        (((16:R[X]) • FourRootTraceCoefficient318.rootProduct
          (DVRNormalizedInfinityOrder318.coefficient R d a))*x) :=
  FourRootTraceCoefficient318.trace_eq _ x
end OriginalAllPrimeFiniteDuality318
