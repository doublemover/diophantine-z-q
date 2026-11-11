module
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
public section
noncomputable section
namespace OpenRestrictionImages318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

variable {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]

/-- Open restriction is also a right adjoint: its displayed definition is
pushforward on the open-subset site with the actual inverse structure map.
Together with the independently supplied left adjunction this preserves
both kernels and cokernels, rather than just cokernels. -/
instance restrictionRightAdjoint : (Scheme.Modules.restrictFunctor j).IsRightAdjoint := by
  unfold Scheme.Modules.restrictFunctor
  infer_instance

/-- Restriction of the actual categorical image, not the image of sections. -/
@[expose] def imageIso {M N : Y.Modules} (f : M ⟶ N) :
    image ((Scheme.Modules.restrictFunctor j).map f) ≅
      (Scheme.Modules.restrictFunctor j).obj (image f) :=
  CategoryTheory.PreservesImage.iso (Scheme.Modules.restrictFunctor j) f

@[reassoc] lemma imageIso_inclusion {M N : Y.Modules} (f : M ⟶ N) :
    (imageIso j f).hom ≫ (Scheme.Modules.restrictFunctor j).map (image.ι f) =
      image.ι ((Scheme.Modules.restrictFunctor j).map f) :=
  CategoryTheory.PreservesImage.hom_comp_map_image_ι _ _

@[reassoc] lemma imageIso_factor {M N : Y.Modules} (f : M ⟶ N) :
    factorThruImage ((Scheme.Modules.restrictFunctor j).map f) ≫
      (imageIso j f).hom = (Scheme.Modules.restrictFunctor j).map (factorThruImage f) :=
  CategoryTheory.PreservesImage.factorThruImage_comp_hom _ _
end OpenRestrictionImages318
