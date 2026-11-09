module
public import IntegralBranchLocalization318
public import ContactFrameNormalization318
public import SquareCoordinateDifferential318
public section
noncomputable section
namespace IntegralBranchCoordinates318
open Polynomial IntegralSourceBranches318 IntegralBranchFrames318 IntegralBranchLocalization318
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ) (i : Fin 4)
abbrev B := Localization.Away (IntegralBranchDenominatorCover318.denominator R c i)
@[expose] def rootCoordinate : BranchBase R c i :=
  (LinearRootCoordinate318.coordinateEquiv (c i) (contacts R i)).symm X
@[expose] def openCoordinate : OpenOrder R c i :=
  algebraMap (OpenBase R c i) (OpenOrder R c i)
    (algebraMap (BranchBase R c i) (OpenBase R c i) (rootCoordinate R c i))
@[expose] def sourceCoordinate : B R c i :=
  (sourceLocalizationEquiv R c i).symm (openCoordinate R c i)
@[expose] def sourceT : B R c i :=
  algebraMap (SourceOrder R c) (B R c i) (algebraMap R[X] (SourceOrder R c) X)

theorem root_normalized :
    rootFrame R c i (KaehlerDifferential.D R (BranchBase R c i) (rootCoordinate R c i)) = 1 := by
  rw [rootFrame,rootCoordinate,ContactFrameNormalization318.ofAlgEquiv_D_image,
    KaehlerDifferential.polynomialEquiv_D,Polynomial.derivative_X,map_one]

theorem open_normalized (h2 : IsUnit (2 : R)) :
    frame R c i h2 (KaehlerDifferential.D R (OpenOrder R c i) (openCoordinate R c i)) = 1 := by
  letI : Algebra.Etale (OpenBase R c i) (OpenOrder R c i) :=
    (finite_free_etale R c h2 i).2.2
  change LocalizedKaehlerFrame318.etaleFrame (baseFrame R c i)
    (KaehlerDifferential.D R _ (algebraMap _ _ _)) = 1
  rw [LocalizedKaehlerFrame318.etaleFrame_D]
  change algebraMap (OpenBase R c i) (OpenOrder R c i)
    (LocalizedKaehlerFrame318.localFrame _ (rootFrame R c i)
      (KaehlerDifferential.D R _ (algebraMap _ _ _))) = 1
  rw [LocalizedKaehlerFrame318.localFrame_D,root_normalized,map_one]

theorem source_normalized (h2 : IsUnit (2 : R)) :
    sourceFrame R c i h2 (KaehlerDifferential.D R (B R c i) (sourceCoordinate R c i)) = 1 := by
  rw [sourceFrame,sourceCoordinate,ContactFrameNormalization318.ofAlgEquiv_D_image,
    open_normalized,map_one]

theorem coordinate_square :
    sourceT R c i - algebraMap R (B R c i) (contacts R i) =
      algebraMap R (B R c i) (↑(c i)⁻¹ : R) * sourceCoordinate R c i ^ 2 := by
  apply (sourceLocalizationEquiv R c i).injective
  rw [map_sub,map_mul,map_pow,AlgEquiv.commutes,AlgEquiv.commutes]
  rw [sourceCoordinate,AlgEquiv.apply_symm_apply,sourceT,
    sourceLocalizationEquiv_on_source,sourceMap_on_polynomial]
  have h := congrArg
    ((algebraMap (OpenBase R c i) (OpenOrder R c i)).comp
      (algebraMap (BranchBase R c i) (OpenBase R c i)))
    (LinearRootCoordinate318.contact_square (c i) (contacts R i))
  have hr : rootCoordinate R c i = AdjoinRoot.root
      (QuadraticPresentation318.polynomial
        (LinearRootCoordinate318.parameter (c i) (contacts R i))) :=
    LinearRootCoordinate318.inverse_X (c i) (contacts R i)
  have hC (a : R) : algebraMap R[X] (OpenOrder R c i) (C a) =
      algebraMap R (OpenOrder R c i) a :=
    (IsScalarTower.algebraMap_apply R R[X] (OpenOrder R c i) a).symm
  simpa only [RingHom.comp_apply,map_sub,map_mul,map_pow,openCoordinate,hr,
    ←IsScalarTower.algebraMap_apply,hC] using h

/-- The exact original derivative coefficient retains the factor two and twist inverse. -/
theorem frame_D_sourceT (h2 : IsUnit (2 : R)) :
    sourceFrame R c i h2 (KaehlerDifferential.D R (B R c i) (sourceT R c i)) =
      2 * algebraMap R (B R c i) (↑(c i)⁻¹ : R) * sourceCoordinate R c i :=
  SquareCoordinateDifferential318.frame_D_of_square (sourceFrame R c i h2)
    (sourceT R c i) (sourceCoordinate R c i) (contacts R i) (↑(c i)⁻¹ : R)
    (coordinate_square R c i) (source_normalized R c i h2)

end IntegralBranchCoordinates318
