module
public import ContactDifferentialFrames318
public section
noncomputable section
namespace ContactFrameNormalization318
open TensorProduct Polynomial
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
section Generic
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]

theorem ofAlgEquiv_D_image (f : S ≃ₐ[R] T) (e : KaehlerDifferential R S ≃ₗ[S] S) (s : S) :
    EtaleDifferentialFrame318.ofAlgEquiv f e (KaehlerDifferential.D R T (f s)) =
      f (e (KaehlerDifferential.D R S s)) := by
  change f (e (AlgHomDifferential318.map f.symm.toAlgHom (KaehlerDifferential.D R T (f s))))=_
  rw [AlgHomDifferential318.map_D]
  change f (e (KaehlerDifferential.D R S (f.symm (f s))))=_
  rw [f.symm_apply_apply]

variable [Algebra S T] [IsScalarTower R S T] [Algebra.FormallyEtale S T]
theorem ofFormallyEtale_D (e : KaehlerDifferential R S ≃ₗ[S] S) (s : S) :
    EtaleDifferentialFrame318.ofFormallyEtale e
      (KaehlerDifferential.D R T (algebraMap S T s))=
        algebraMap S T (e (KaehlerDifferential.D R S s)) := by
  simp only [EtaleDifferentialFrame318.ofFormallyEtale,LinearEquiv.trans_apply,
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap,
    TensorProduct.AlgebraTensorModule.congr_tmul,LinearEquiv.refl_apply,
    TensorProduct.AlgebraTensorModule.rid_tmul,Algebra.smul_def,mul_one]
end Generic

variable (c : Fin 4 → ℚˣ)
@[expose] def branchCoordinate (i : Fin 4) : SourceFiniteBranch318.BranchBase c i :=
  (LinearRootCoordinate318.coordinateEquiv (c i) (LinearContactSquareclass318.contacts i)).symm X

theorem branch_coordinate_normalized (i : Fin 4) :
    ContactDifferentialFrames318.branchBaseFrame c i
      (KaehlerDifferential.D ℚ (SourceFiniteBranch318.BranchBase c i) (branchCoordinate c i))=1 := by
  rw [ContactDifferentialFrames318.branchBaseFrame,branchCoordinate,ofAlgEquiv_D_image,
    KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X,map_one]

/-- Exact ramified-root coordinate on the etale branch order. -/
@[expose] def branchOrderCoordinate (i : Fin 4) : SourceFiniteBranch318.OpenOrder c i :=
  algebraMap (SourceFiniteBranch318.OpenBase c i) (SourceFiniteBranch318.OpenOrder c i)
    (algebraMap (SourceFiniteBranch318.BranchBase c i) (SourceFiniteBranch318.OpenBase c i)
      (branchCoordinate c i))

theorem branch_order_normalized (i : Fin 4) :
    ContactDifferentialFrames318.branchFrame c i
      (KaehlerDifferential.D ℚ (SourceFiniteBranch318.OpenOrder c i) (branchOrderCoordinate c i))=1 := by
  letI := Algebra.FormallyEtale.of_isLocalization
    (Rₘ:=SourceFiniteBranch318.OpenBase c i)
      (Submonoid.powers (FiniteBranchChart318.denominator (c i) (LinearContactSquareclass318.contacts i)
        (SourceFiniteBranch318.otherTwist c i) (SourceFiniteBranch318.otherContact i)))
  letI : Algebra.Etale (SourceFiniteBranch318.OpenBase c i) (SourceFiniteBranch318.OpenOrder c i) :=
    (SourceFiniteBranch318.source_finite_branch c i).2.2.1
  change EtaleDifferentialFrame318.ofFormallyEtale (ContactDifferentialFrames318.branchOpenBaseFrame c i)
    (KaehlerDifferential.D ℚ _ (algebraMap _ _ _))=1
  rw [ofFormallyEtale_D]
  change algebraMap _ _ (EtaleDifferentialFrame318.ofFormallyEtale
    (ContactDifferentialFrames318.branchBaseFrame c i) (KaehlerDifferential.D ℚ _ (algebraMap _ _ _)))=1
  rw [ofFormallyEtale_D,branch_coordinate_normalized,map_one,map_one]

@[expose] def sourceCoordinate (i : Fin 4) :
    Localization.Away (SourceDenominatorCover318.denominator c i) :=
  (SourceBranchLocalization318.sourceLocalizationEquiv c i).symm (branchOrderCoordinate c i)

theorem source_coordinate_normalized (i : Fin 4) :
    ContactDifferentialFrames318.sourceLocalizationFrame c i
      (KaehlerDifferential.D ℚ (Localization.Away (SourceDenominatorCover318.denominator c i))
        (sourceCoordinate c i))=1 := by
  rw [ContactDifferentialFrames318.sourceLocalizationFrame,sourceCoordinate,ofAlgEquiv_D_image,
    branch_order_normalized,map_one]

@[expose] def infinityCoordinate : InfinityGlobalChart318.InfinityOrder c :=
  algebraMap (InfinityOpenChart318.OpenBase c) (InfinityOpenChart318.OpenOrder c)
    (algebraMap ℚ[X] (InfinityOpenChart318.OpenBase c) X)

theorem infinity_coordinate_normalized :
    ContactDifferentialFrames318.infinityFrame c
      (KaehlerDifferential.D ℚ (InfinityGlobalChart318.InfinityOrder c) (infinityCoordinate c))=1 := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ:=InfinityOpenChart318.OpenBase c)
    (Submonoid.powers (InfinityOpenChart318.denominator c))
  letI : Algebra.Etale (InfinityOpenChart318.OpenBase c) (InfinityOpenChart318.OpenOrder c) :=
    (InfinityOpenChart318.finite_free_etale_rank_eight c).2.2.1
  change EtaleDifferentialFrame318.ofFormallyEtale (ContactDifferentialFrames318.infinityBaseFrame c)
    (KaehlerDifferential.D ℚ _ (algebraMap _ _ _))=1
  rw [ofFormallyEtale_D]
  change algebraMap _ _ (EtaleDifferentialFrame318.ofFormallyEtale (KaehlerDifferential.polynomialEquiv ℚ)
    (KaehlerDifferential.D ℚ _ (algebraMap _ _ X)))=1
  rw [ofFormallyEtale_D,KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X,map_one,map_one]
end ContactFrameNormalization318
