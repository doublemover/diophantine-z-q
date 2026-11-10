module
public import PELOriginalDoublingFactor318
public section
noncomputable section
namespace PELOriginalDoublingTopology318
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open PELOriginalCharacterQuotient318 PELOriginalCharacterTopology318
open PELOriginalDeckTwoTorsion318 PELOriginalDoublingFactor318
open ComplexAffineFreeTranslation318
set_option maxHeartbeats 2400000
variable (i : Fin 4) (L : AddSubgroup ℂ)
variable (u : InvolutionBase i ≃ₜ Torus L)
variable (basis : RankTwoComplexHalfPeriods318.Coordinates ≃+ L)
variable (hlift : AffineLifts i L u.toEquiv)

/-- Continuity of the actual descended doubling factor follows through
the literal character quotient from the original uniformization square. -/
theorem doublingFactor_continuous :
    Continuous (doublingFactor i L u.toEquiv basis hlift) :=
  ((u.continuous.comp (toInvolution_continuous i)).const_smul (2:ℤ)).quotient_lift _

/-- No topological identification of an arbitrary isogenous torus is
assumed: the exact factor has been constructed and is a homeomorphism to
the SAME lattice quotient. A holomorphic uniformization and analytic
compatibility are still needed before asserting equal elliptic j. -/
@[expose] def characterHomeomorph [DiscreteTopology L] : CharacterBase i ≃ₜ Torus L := by
  letI : IsClosed (L : Set ℂ) := AddSubgroup.isClosed_of_discreteTopology
  exact (characterEquiv i L u.toEquiv basis hlift).toHomeomorphOfContinuousClosed
    (doublingFactor_continuous i L u basis hlift)
    (doublingFactor_continuous i L u basis hlift).isClosedMap

theorem original_doubling_square [DiscreteTopology L] (p : InvolutionBase i) :
    characterHomeomorph i L u basis hlift (toCharacterBase i p)=(2:ℤ) • u p :=
  doublingFactor_square i L u.toEquiv basis hlift p
end PELOriginalDoublingTopology318
