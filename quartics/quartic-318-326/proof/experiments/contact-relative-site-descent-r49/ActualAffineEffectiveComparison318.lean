module
public import ActualCanonicalOverlap318
public section
noncomputable section
namespace ActualAffineEffectiveComparison318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ActualAffineDoubleNerve318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] [Module.FaithfullyFlat R S]
  (L : Line (Spec S))
  (τ : ActualAffineSheafData318.firstObject R S L ⟶ ActualAffineSheafData318.secondObject R S L)
  (hdiag : ActualAffineSheafData318.Diagonal R S L τ)
  (htriple : ActualAffineSheafData318.Cocycle R S L τ)
abbrev line := ActualAffineLineReconstruction318.line R S L τ hdiag htriple
abbrev comparison := ActualAffineLineReconstruction318.pullbackIso R S L τ hdiag htriple

/-- The exact reconstruction comparison carries the canonical overlap on
the genuine categorical double to the unchanged original input overlap.
The original scheme isomorphism reflects the tensor-spectrum calculation. -/
lemma original_overlap :
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map
        (comparison R S L τ hdiag htriple).inv ≫
      CanonicalSheafOverlap318.actual (line R S L τ hdiag htriple).object (baseMap R S) ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map
        (comparison R S L τ hdiag htriple).hom = τ := by
  apply SheafIsoTransport318.transport_injective L.object (doubleIso R S).symm
    (ActualOverlapDiagram318.first (baseMap R S)) (ActualOverlapDiagram318.second (baseMap R S))
    (Spec.map (AffineModuleBaseChange318.leftMap R S S))
    (Spec.map (AffineModuleBaseChange318.rightMap R S S)) (inverse_first R S) (inverse_second R S)
  rw [SheafIsoTransport318.conjugation]
  rw [ActualCanonicalOverlap318.transport]
  exact ReconstructedOverlapCompatibility318.original_overlap R S L
    (ActualAffineTensorTransport318.overlap R S L τ)
    (ActualAffineTensorLaws318.diagonal R S L τ hdiag)
    (ActualAffineTensorLaws318.triple R S L τ htriple)

/-- The actual displayed isomorphism is compatible with the original
geometric descent datum on the actual categorical fiber product. -/
lemma comparison_commutes :
    CanonicalSheafOverlap318.actual (line R S L τ hdiag htriple).object (baseMap R S) ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map
        (comparison R S L τ hdiag htriple).hom =
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map
      (comparison R S L τ hdiag htriple).hom ≫ τ := by
  rw [← original_overlap R S L τ hdiag htriple]
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id,
    Functor.map_id, Category.id_comp]

/-- Effective descent with its exact original geometric compatibility
square, for a faithfully flat morphism of affine schemes. The diagonal
and triple laws are the original categorical-scheme laws; no module or
scalar-extension coalgebra law is an input. -/
theorem effective (hdiag : ActualAffineSheafData318.Diagonal R S L τ)
    (htriple : ActualAffineSheafData318.Cocycle R S L τ) : ∃ (K : Line (Spec R))
    (e : (Scheme.Modules.pullback (baseMap R S)).obj K.object ≅ L.object),
    CanonicalSheafOverlap318.actual K.object (baseMap R S) ≫
      (Scheme.Modules.pullback (ActualOverlapDiagram318.second (baseMap R S))).map e.hom =
    (Scheme.Modules.pullback (ActualOverlapDiagram318.first (baseMap R S))).map e.hom ≫ τ :=
  ⟨line R S L τ hdiag htriple, comparison R S L τ hdiag htriple,
    comparison_commutes R S L τ hdiag htriple⟩
end ActualAffineEffectiveComparison318
