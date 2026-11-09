module
public import RelativeAffineDualPresentation318
public section
noncomputable section
namespace RelativeAffinePointedTriviality318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RelativeAffineDualPresentation318
universe u
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable (L : DualNumberScheme318.Deformation R (baseMap R S))
/-- Pull the unchanged original pointed line to its actual affine tensor model. -/
@[expose] def affineDeformation : PointedLineDeformation318.Deformation
    (Spec.map (CommRingCat.ofHom (DualNumberScalarExtension318.reduction R S))) :=
  PointedLinePullback318.deformation _ _ (affineIso R S).inv (𝟙 _)
    (by simpa only [Category.id_comp] using reduction_affineIso_inv R S) L
@[expose] def affineFrame : SheafOfModules.unit (Spec (CommRingCat.of (Tensor R S))).ringCatSheaf ≅
    (affineDeformation R S L).line.object :=
  OriginalAffineSquareZeroFrame318.frame
    (CommRingCat.ofHom (DualNumberScalarExtension318.reduction R S))
    (affineDeformation R S L).line (affineDeformation R S L).trivialization
    (DualNumberScalarExtension318.sectionMap R S) (DualNumberScalarExtension318.reduction_section R S)
    (DualNumberScalarExtension318.epsilon R S) (DualNumberScalarExtension318.epsilon_square R S)
    (DualNumberScalarExtension318.reduction_kernel R S)
/-- A genuine original sheaf frame on the original categorical thickening. -/
@[expose] def frame : SheafOfModules.unit (Thick R S).ringCatSheaf ≅ L.line.object :=
  (IdentityCotangent318.pullbackUnitIso (affineIso R S).hom).symm ≪≫
    (Scheme.Modules.pullback (affineIso R S).hom).mapIso (affineFrame R S L) ≪≫
    (Scheme.Modules.pullbackComp (affineIso R S).hom (affineIso R S).inv).app L.line.object ≪≫
    (Scheme.Modules.pullbackCongr (affineIso R S).hom_inv_id).app L.line.object ≪≫
    (Scheme.Modules.pullbackId (Thick R S)).app L.line.object
/-- The supplied special-fiber frame is preserved by the original split
projection, not merely forgotten after constructing an unpointed frame. -/
@[expose] def pointedIso : PointedLineDeformation318.PointedIso
    (DualNumberScheme318.reduction R (baseMap R S)) L
    (PointedLineDeformation318.trivial (DualNumberScheme318.reduction R (baseMap R S))) :=
  SplitReductionPointedKernel318.pointedIsoOfIso _
    (pullback.fst (baseMap R S) (DualNumberScheme318.structureMap R))
    (DualNumberScheme318.reduction_fst R (baseMap R S)) L _ (frame R S L).symm
lemma class_trivial : PointedLineDeformation318.classOf _ L =
    PointedLineDeformation318.classOf _
      (PointedLineDeformation318.trivial (DualNumberScheme318.reduction R (baseMap R S))) :=
  (PointedLineDeformation318.classOf_eq_iff _ _ _).2 ⟨pointedIso R S L⟩
instance pointed_subsingleton : Subsingleton (DualNumberScheme318.Class R (baseMap R S)) := by
  refine ⟨fun a b => ?_⟩
  induction a using Quotient.inductionOn with
  | h L =>
    induction b using Quotient.inductionOn with
    | h M => exact (class_trivial R S L).trans (class_trivial R S M).symm
end RelativeAffinePointedTriviality318
