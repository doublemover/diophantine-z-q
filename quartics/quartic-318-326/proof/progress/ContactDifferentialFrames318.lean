module
public import EtaleDifferentialFrame318
public import SourceBranchLocalization318
public import InfinityGlobalScheme318
public section
noncomputable section
namespace ContactDifferentialFrames318
open Polynomial
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

@[expose] def branchBaseFrame (i : Fin 4) :
    KaehlerDifferential ℚ (SourceFiniteBranch318.BranchBase c i) ≃ₗ[SourceFiniteBranch318.BranchBase c i]
      SourceFiniteBranch318.BranchBase c i :=
  EtaleDifferentialFrame318.ofAlgEquiv
    (LinearRootCoordinate318.coordinateEquiv (c i) (LinearContactSquareclass318.contacts i)).symm
      (KaehlerDifferential.polynomialEquiv ℚ)

@[expose] def branchOpenBaseFrame (i : Fin 4) :
    KaehlerDifferential ℚ (SourceFiniteBranch318.OpenBase c i) ≃ₗ[SourceFiniteBranch318.OpenBase c i]
      SourceFiniteBranch318.OpenBase c i := by
  letI := Algebra.FormallyEtale.of_isLocalization
    (Rₘ:=SourceFiniteBranch318.OpenBase c i)
      (Submonoid.powers (FiniteBranchChart318.denominator (c i) (LinearContactSquareclass318.contacts i)
        (SourceFiniteBranch318.otherTwist c i) (SourceFiniteBranch318.otherContact i)))
  exact EtaleDifferentialFrame318.ofFormallyEtale (branchBaseFrame c i)

/-- Actual branch-chart differentials are freely generated in the genuine
ramified root coordinate, not in the invalid parameter t at its branch point. -/
@[expose] def branchFrame (i : Fin 4) :
    KaehlerDifferential ℚ (SourceFiniteBranch318.OpenOrder c i) ≃ₗ[SourceFiniteBranch318.OpenOrder c i]
      SourceFiniteBranch318.OpenOrder c i := by
  letI : Algebra.Etale (SourceFiniteBranch318.OpenBase c i) (SourceFiniteBranch318.OpenOrder c i) :=
    (SourceFiniteBranch318.source_finite_branch c i).2.2.1
  exact EtaleDifferentialFrame318.ofFormallyEtale (branchOpenBaseFrame c i)

/-- The frames belong to the actual principal localizations of SourceOrder. -/
@[expose] def sourceLocalizationFrame (i : Fin 4) :
    KaehlerDifferential ℚ (Localization.Away (SourceDenominatorCover318.denominator c i)) ≃ₗ[
      Localization.Away (SourceDenominatorCover318.denominator c i)]
        Localization.Away (SourceDenominatorCover318.denominator c i) :=
  EtaleDifferentialFrame318.ofAlgEquiv (SourceBranchLocalization318.sourceLocalizationEquiv c i).symm
    (branchFrame c i)

@[expose] def infinityBaseFrame :
    KaehlerDifferential ℚ (InfinityOpenChart318.OpenBase c) ≃ₗ[InfinityOpenChart318.OpenBase c]
      InfinityOpenChart318.OpenBase c := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ:=InfinityOpenChart318.OpenBase c)
    (Submonoid.powers (InfinityOpenChart318.denominator c))
  exact EtaleDifferentialFrame318.ofFormallyEtale (KaehlerDifferential.polynomialEquiv ℚ)

/-- The actual attached infinity neighborhood has a free intrinsic algebraic
cotangent frame in its u coordinate. -/
@[expose] def infinityFrame :
    KaehlerDifferential ℚ (InfinityGlobalChart318.InfinityOrder c) ≃ₗ[InfinityGlobalChart318.InfinityOrder c]
      InfinityGlobalChart318.InfinityOrder c := by
  letI : Algebra.Etale (InfinityOpenChart318.OpenBase c) (InfinityOpenChart318.OpenOrder c) :=
    (InfinityOpenChart318.finite_free_etale_rank_eight c).2.2.1
  exact EtaleDifferentialFrame318.ofFormallyEtale (infinityBaseFrame c)
end ContactDifferentialFrames318
