module
public import EtaleDifferentialFrame318
public import SourceBranchLocalization318
public import InfinityOpenChart318
public section
noncomputable section
namespace ContactDifferentialFrames318
open Polynomial KaehlerDifferential SourceFiniteBranch318
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

@[expose] def branchBaseFrame (i : Fin 4) :
    KaehlerDifferential ℚ (BranchBase c i) ≃ₗ[BranchBase c i] BranchBase c i :=
  EtaleDifferentialFrame318.ofAlgEquiv
    (LinearRootCoordinate318.coordinateEquiv (c i)
      (LinearContactSquareclass318.contacts i)).symm (KaehlerDifferential.polynomialEquiv ℚ)

@[expose] def branchOpenBaseFrame (i : Fin 4) :
    KaehlerDifferential ℚ (OpenBase c i) ≃ₗ[OpenBase c i] OpenBase c i := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := OpenBase c i)
    (Submonoid.powers (FiniteBranchChart318.denominator (c i)
      (LinearContactSquareclass318.contacts i) (otherTwist c i) (otherContact i)))
  exact EtaleDifferentialFrame318.ofFormallyEtale (branchBaseFrame c i)

@[expose] def branchFrame (i : Fin 4) :
    KaehlerDifferential ℚ (OpenOrder c i) ≃ₗ[OpenOrder c i] OpenOrder c i := by
  letI : Algebra.Etale (OpenBase c i) (OpenOrder c i) := (source_finite_branch c i).2.2.1
  exact EtaleDifferentialFrame318.ofFormallyEtale (branchOpenBaseFrame c i)

@[expose] def sourceLocalizationFrame (i : Fin 4) :
    KaehlerDifferential ℚ (Localization.Away (SourceDenominatorCover318.denominator c i)) ≃ₗ[
      Localization.Away (SourceDenominatorCover318.denominator c i)]
        Localization.Away (SourceDenominatorCover318.denominator c i) :=
  EtaleDifferentialFrame318.ofAlgEquiv
    (SourceBranchLocalization318.sourceLocalizationEquiv c i).symm (branchFrame c i)

@[expose] def infinityBaseFrame :
    KaehlerDifferential ℚ (InfinityOpenChart318.OpenBase c) ≃ₗ[
      InfinityOpenChart318.OpenBase c] InfinityOpenChart318.OpenBase c := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := InfinityOpenChart318.OpenBase c)
    (Submonoid.powers (InfinityOpenChart318.denominator c))
  exact EtaleDifferentialFrame318.ofFormallyEtale (KaehlerDifferential.polynomialEquiv ℚ)

@[expose] def infinityFrame :
    KaehlerDifferential ℚ (InfinityOpenChart318.OpenOrder c) ≃ₗ[
      InfinityOpenChart318.OpenOrder c] InfinityOpenChart318.OpenOrder c := by
  letI : Algebra.Etale (InfinityOpenChart318.OpenBase c) (InfinityOpenChart318.OpenOrder c) :=
    (InfinityOpenChart318.finite_free_etale_rank_eight c).2.2.1
  exact EtaleDifferentialFrame318.ofFormallyEtale (infinityBaseFrame c)

end ContactDifferentialFrames318
