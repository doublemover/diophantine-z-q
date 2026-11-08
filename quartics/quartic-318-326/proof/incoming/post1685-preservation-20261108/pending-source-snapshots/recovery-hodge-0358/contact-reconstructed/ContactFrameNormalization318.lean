module
public import ContactDifferentialFrames318
public section
noncomputable section
namespace EtaleDifferentialFrame318
open KaehlerDifferential
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

theorem ofAlgEquiv_D_image (f : S ≃ₐ[R] T)
    (e : KaehlerDifferential R S ≃ₗ[S] S) (s : S) :
    ofAlgEquiv f e (D R T (f s)) = f (e (D R S s)) := by
  change f (e (AlgHomDifferential318.map f.symm.toAlgHom (D R T (f s)))) = _
  rw [AlgHomDifferential318.map_D]
  change f (e (D R S (f.symm (f s)))) = _
  rw [f.symm_apply_apply]

variable [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T]
theorem ofFormallyEtale_D (e : KaehlerDifferential R S ≃ₗ[S] S) (s : S) :
    ofFormallyEtale (T:=T) e (D R T (algebraMap S T s)) =
      algebraMap S T (e (D R S s)) :=
  LocalizedKaehlerFrame318.etaleFrame_D e s
end EtaleDifferentialFrame318

namespace ContactFrameNormalization318
open Polynomial KaehlerDifferential SourceFiniteBranch318 ContactDifferentialFrames318
set_option maxHeartbeats 700000
set_option synthInstance.maxSize 256
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (c : Fin 4 → ℚˣ)

@[expose] def branchCoordinate (i : Fin 4) : BranchBase c i :=
  (LinearRootCoordinate318.coordinateEquiv (c i)
    (LinearContactSquareclass318.contacts i)).symm X

@[expose] def branchOpenCoordinate (i : Fin 4) : OpenBase c i :=
  algebraMap (BranchBase c i) (OpenBase c i) (branchCoordinate c i)

@[expose] def branchOrderCoordinate (i : Fin 4) : OpenOrder c i :=
  algebraMap (OpenBase c i) (OpenOrder c i) (branchOpenCoordinate c i)

@[expose] def sourceCoordinate (i : Fin 4) :
    Localization.Away (SourceDenominatorCover318.denominator c i) :=
  (SourceBranchLocalization318.sourceLocalizationEquiv c i).symm (branchOrderCoordinate c i)

@[expose] def infinityBaseCoordinate : InfinityOpenChart318.OpenBase c :=
  algebraMap ℚ[X] (InfinityOpenChart318.OpenBase c) X

@[expose] def infinityCoordinate : InfinityOpenChart318.OpenOrder c :=
  algebraMap (InfinityOpenChart318.OpenBase c) (InfinityOpenChart318.OpenOrder c)
    (infinityBaseCoordinate c)

theorem branchBaseFrame_coordinate_normalized (i : Fin 4) :
    branchBaseFrame c i (D ℚ (BranchBase c i) (branchCoordinate c i)) = 1 := by
  rw [branchBaseFrame,branchCoordinate,EtaleDifferentialFrame318.ofAlgEquiv_D_image]
  simp

theorem branchOpenBaseFrame_coordinate_normalized (i : Fin 4) :
    branchOpenBaseFrame c i (D ℚ (OpenBase c i) (branchOpenCoordinate c i)) = 1 := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := OpenBase c i)
    (Submonoid.powers (FiniteBranchChart318.denominator (c i)
      (LinearContactSquareclass318.contacts i) (otherTwist c i) (otherContact i)))
  change EtaleDifferentialFrame318.ofFormallyEtale (branchBaseFrame c i)
    (D ℚ (OpenBase c i) (algebraMap (BranchBase c i) (OpenBase c i) (branchCoordinate c i))) = 1
  rw [EtaleDifferentialFrame318.ofFormallyEtale_D,branchBaseFrame_coordinate_normalized,map_one]

theorem branchFrame_coordinate_normalized (i : Fin 4) :
    branchFrame c i (D ℚ (OpenOrder c i) (branchOrderCoordinate c i)) = 1 := by
  letI : Algebra.Etale (OpenBase c i) (OpenOrder c i) := (source_finite_branch c i).2.2.1
  change EtaleDifferentialFrame318.ofFormallyEtale (branchOpenBaseFrame c i)
    (D ℚ (OpenOrder c i) (algebraMap (OpenBase c i) (OpenOrder c i) (branchOpenCoordinate c i))) = 1
  rw [EtaleDifferentialFrame318.ofFormallyEtale_D,branchOpenBaseFrame_coordinate_normalized,map_one]

theorem sourceLocalizationFrame_coordinate_normalized (i : Fin 4) :
    sourceLocalizationFrame c i
      (D ℚ (Localization.Away (SourceDenominatorCover318.denominator c i)) (sourceCoordinate c i)) = 1 := by
  rw [sourceLocalizationFrame,sourceCoordinate,EtaleDifferentialFrame318.ofAlgEquiv_D_image,
    branchFrame_coordinate_normalized,map_one]

theorem infinityBaseFrame_coordinate_normalized :
    infinityBaseFrame c (D ℚ (InfinityOpenChart318.OpenBase c) (infinityBaseCoordinate c)) = 1 := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := InfinityOpenChart318.OpenBase c)
    (Submonoid.powers (InfinityOpenChart318.denominator c))
  change EtaleDifferentialFrame318.ofFormallyEtale (KaehlerDifferential.polynomialEquiv ℚ)
    (D ℚ (InfinityOpenChart318.OpenBase c) (algebraMap ℚ[X] (InfinityOpenChart318.OpenBase c) X)) = 1
  rw [EtaleDifferentialFrame318.ofFormallyEtale_D]
  simp

theorem infinityFrame_coordinate_normalized :
    infinityFrame c (D ℚ (InfinityOpenChart318.OpenOrder c) (infinityCoordinate c)) = 1 := by
  letI : Algebra.Etale (InfinityOpenChart318.OpenBase c) (InfinityOpenChart318.OpenOrder c) :=
    (InfinityOpenChart318.finite_free_etale_rank_eight c).2.2.1
  change EtaleDifferentialFrame318.ofFormallyEtale (infinityBaseFrame c)
    (D ℚ (InfinityOpenChart318.OpenOrder c)
      (algebraMap (InfinityOpenChart318.OpenBase c) (InfinityOpenChart318.OpenOrder c)
        (infinityBaseCoordinate c))) = 1
  rw [EtaleDifferentialFrame318.ofFormallyEtale_D,infinityBaseFrame_coordinate_normalized,map_one]
end ContactFrameNormalization318
