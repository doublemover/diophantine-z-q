module
public import IntegralOverlapSheafCompatibility318
public import Mathlib.AlgebraicGeometry.Limits
public section
noncomputable section
namespace IntegralOverlapOpenImmersions318
open AlgebraicGeometry CategoryTheory
open IntegralSourceBranches318 IntegralInfinityCommonBase318
open IntegralInfinityOverlapRealization318 IntegralOverlapChartMaps318
open scoped TensorProduct
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
local instance infinityAlgebra :
    Algebra (IntegralInfinityChart318.Base R c) (CommonBase R c) :=
  (infinityBaseMap R c).toRingHom.toAlgebra

local instance overlapCommRing : CommRing (Overlap R c) := inferInstance
local instance openOrderCommRing : CommRing (OpenOrder R c 0) := inferInstance
local instance finiteCommRing : CommRing (IntegralBranchCoordinates318.B R c 0) := inferInstance
local instance infinityCommRing : CommRing (IntegralInfinityChart318.Order R c) := inferInstance
local instance sourceCommRing : CommRing (SourceOrder R c) := inferInstance
local instance infinityOverlapCommRing : CommRing
    (CommonBase R c ⊗[IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c) := inferInstance

/-- The actual right inclusion on the finite side is the principal open
already proved algebraically, now as a scheme open immersion. -/
theorem finite_right_open :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (show OpenOrder R c 0 →+* Overlap R c from (Algebra.TensorProduct.includeRight : OpenOrder R c 0 →ₐ[OpenBase R c 0]
        Overlap R c).toRingHom))) := by
  letI := rightAlgebra (OpenBase R c 0) (CommonBase R c) (OpenOrder R c 0)
  letI := finiteOrder_localization R c
  exact IsOpenImmersion.of_isLocalization
    (algebraMap (OpenBase R c 0) (OpenOrder R c 0) (rootOpen R c))

theorem infinity_right_open :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (show IntegralInfinityChart318.Order R c →+*
        (CommonBase R c ⊗[IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c) from (Algebra.TensorProduct.includeRight : IntegralInfinityChart318.Order R c
        →ₐ[IntegralInfinityChart318.Base R c]
          CommonBase R c ⊗[IntegralInfinityChart318.Base R c]
            IntegralInfinityChart318.Order R c).toRingHom))) := by
  letI := rightAlgebra (IntegralInfinityChart318.Base R c) (CommonBase R c)
    (IntegralInfinityChart318.Order R c)
  letI := infinityOrder_localization R c
  exact IsOpenImmersion.of_isLocalization (IntegralInfinityChart318.coordinate R c)

instance finiteMap_open :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (show IntegralBranchCoordinates318.B R c 0 →+* Overlap R c from (finiteMap R c).toRingHom))) := by
  letI := finite_right_open R c
  have he : Spec.map (CommRingCat.ofHom (show IntegralBranchCoordinates318.B R c 0 →+* Overlap R c from (finiteMap R c).toRingHom)) =
      Spec.map (CommRingCat.ofHom
        (show OpenOrder R c 0 →+* Overlap R c from (Algebra.TensorProduct.includeRight : OpenOrder R c 0 →ₐ[OpenBase R c 0]
          Overlap R c).toRingHom)) ≫
      Spec.map (IntegralBranchLocalization318.sourceLocalizationEquiv R c 0).toRingEquiv.toCommRingCatIso.hom := by
    rw [←Spec.map_comp] <;> rfl
  rw [he]
  infer_instance

instance infinityMap_open :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (show IntegralInfinityChart318.Order R c →+* Overlap R c from (infinityMap R c).toRingHom))) := by
  letI := infinity_right_open R c
  have he : Spec.map (CommRingCat.ofHom (show IntegralInfinityChart318.Order R c →+* Overlap R c from (infinityMap R c).toRingHom)) =
      Spec.map (actualOverlapEquiv R c).symm.toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (show IntegralInfinityChart318.Order R c →+*
        (CommonBase R c ⊗[IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c) from (Algebra.TensorProduct.includeRight : IntegralInfinityChart318.Order R c
          →ₐ[IntegralInfinityChart318.Base R c]
            CommonBase R c ⊗[IntegralInfinityChart318.Base R c]
              IntegralInfinityChart318.Order R c).toRingHom)) := by
    rw [←Spec.map_comp] <;> rfl
  rw [he]
  infer_instance

@[expose] def sourceMap : SourceOrder R c →ₐ[R] Overlap R c :=
  (finiteMap R c).comp (IsScalarTower.toAlgHom R (SourceOrder R c)
    (IntegralBranchCoordinates318.B R c 0))

/-- The overlap enters the entire original affine four-root order, not
only its contact-zero neighborhood. -/
instance sourceMap_open :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (show SourceOrder R c →+* Overlap R c from (sourceMap R c).toRingHom))) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c 0)))) :=
    IsOpenImmersion.of_isLocalization (IntegralBranchDenominatorCover318.denominator R c 0)
  have he : Spec.map (CommRingCat.ofHom (show SourceOrder R c →+* Overlap R c from (sourceMap R c).toRingHom)) =
      Spec.map (CommRingCat.ofHom (show IntegralBranchCoordinates318.B R c 0 →+* Overlap R c from (finiteMap R c).toRingHom)) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap (SourceOrder R c) (IntegralBranchCoordinates318.B R c 0))) := by
    rw [←Spec.map_comp] <;> rfl
  rw [he]
  infer_instance
end IntegralOverlapOpenImmersions318
