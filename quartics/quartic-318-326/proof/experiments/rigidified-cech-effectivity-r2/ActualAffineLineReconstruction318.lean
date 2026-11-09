module
public import ActualAffineTensorLaws318
public section
noncomputable section
namespace ActualAffineLineReconstruction318
open AlgebraicGeometry CategoryTheory LineSheafClass318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]
  (L : Line (Spec S))
  (τ : ActualAffineSheafData318.firstObject R S L ⟶ ActualAffineSheafData318.secondObject R S L)
  (hdiag : ActualAffineSheafData318.Diagonal R S L τ)
  (htriple : ActualAffineSheafData318.Cocycle R S L τ)

/-- An original line with actual scheme fiber-product sheaf descent laws
reconstructs an original line over the faithfully flat affine base. Both
geometric law transports and module coalgebra laws are derived, not assumed. -/
@[expose] def line : Line (Spec R) :=
  OriginalGeometricAffineLine318.line R S L (ActualAffineTensorTransport318.overlap R S L τ)
    (ActualAffineTensorLaws318.diagonal R S L τ hdiag)
    (ActualAffineTensorLaws318.triple R S L τ htriple)

/-- The reconstructed actual base line pulls back to the unchanged input
line, through the original reconstruction comparison. -/
@[expose] def pullbackIso :
    (LineSheafPullback318.line (Spec.map (AffineCoalgebraLine318.ringMap R S))
      (line R S L τ hdiag htriple)).object ≅ L.object :=
  OriginalGeometricAffineLine318.pullbackIso R S L (ActualAffineTensorTransport318.overlap R S L τ)
    (ActualAffineTensorLaws318.diagonal R S L τ hdiag)
    (ActualAffineTensorLaws318.triple R S L τ htriple)
end ActualAffineLineReconstruction318
