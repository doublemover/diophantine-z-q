module
public import OriginalTensorPullbackArbitraryFrameNaturality318
public import LineFrameIsoTransport318
public section
noncomputable section
namespace OriginalFrameCoordinateExt318
open AlgebraicGeometry CategoryTheory
universe u
variable {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
  (e d : SheafOfModules.unit U.toScheme.ringCatSheaf ≅ M.restrict U.ι)
/-- Actual full chart frames are detected by their inverse coordinates
on EVERY ambient subopen. No affine or pointwise detection assumption. -/
lemma inverse_coordinates
    (h : ∀ (Z : X.Opens) (hZ : Z≤U) (s : Γ(M,Z)),
      (OpenLineFrameCoordinates318.frame M U e Z hZ).symm s=
        (OpenLineFrameCoordinates318.frame M U d Z hZ).symm s) : e=d := by
  have hi : e.symm=d.symm := by
    apply Iso.ext
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    have he := h (U.ι ''ᵁ W) (by simpa using U.ι.image_le_opensRange W) s
    simpa only [LineFrameChartCoordinates318.inverse_value,
      LineFrameChartCoordinates318.over_inv_app] using he
  simpa only [Iso.symm_symm] using congrArg Iso.symm hi
lemma coordinates
    (h : ∀ (Z : X.Opens) (hZ : Z≤U),
      OpenLineFrameCoordinates318.frame M U e Z hZ=
        OpenLineFrameCoordinates318.frame M U d Z hZ) : e=d := by
  apply inverse_coordinates M U e d
  intro Z hZ s
  rw [h Z hZ]
end OriginalFrameCoordinateExt318
