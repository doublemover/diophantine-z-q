module
public import ActualAffineTensorTransport318
public section
noncomputable section
namespace ActualAffineTensorLaws318
open AlgebraicGeometry CategoryTheory LineSheafClass318 AffineModuleBaseChange318
open AffineCechRings318 ActualAffineDoubleNerve318 ActualAffineTripleMaps318 ActualAffineTripleNerve318
open ActualAffineTensorTransport318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (L : Line (Spec S))
  (τ : ActualAffineSheafData318.firstObject R S L ⟶ ActualAffineSheafData318.secondObject R S L)

/-- The actual scheme fiber-product sheaf cocycle becomes exactly the
original tensor-spectrum sheaf cocycle, through canonical transport. -/
lemma triple (hτ : ActualAffineSheafData318.Cocycle R S L τ) :
    OriginalGeometricTriple318.Cocycle R S L (overlap R S L τ) := by
  have h01 := face R S L τ (ActualOverlapDiagram318.pair01 (baseMap R S)) (map12 R S)
    (ActualOverlapDiagram318.vertex0 (baseMap R S)) (ActualOverlapDiagram318.vertex1 (baseMap R S))
    (vertex1 R S) (vertex2 R S) (inverse_pair01 R S) rfl rfl
    (toActual_vertex0 R S) (toActual_vertex1 R S) (map12_left R S) (map12_right R S)
  have h12 := face R S L τ (ActualOverlapDiagram318.pair12 (baseMap R S)) (map23 R S)
    (ActualOverlapDiagram318.vertex1 (baseMap R S)) (ActualOverlapDiagram318.vertex2 (baseMap R S))
    (vertex2 R S) (vertex3 R S) (inverse_pair12 R S)
    (ActualOverlapDiagram318.middle_condition (baseMap R S)).symm rfl
    (toActual_vertex1 R S) (toActual_vertex2 R S) (map23_left R S) (map23_right R S)
  have h02 := face R S L τ (ActualOverlapDiagram318.pair02 (baseMap R S)) (map13 R S)
    (ActualOverlapDiagram318.vertex0 (baseMap R S)) (ActualOverlapDiagram318.vertex2 (baseMap R S))
    (vertex1 R S) (vertex3 R S) (inverse_pair02 R S)
    (ActualOverlapDiagram318.pair02_first (baseMap R S))
    (ActualOverlapDiagram318.pair02_second (baseMap R S))
    (toActual_vertex0 R S) (toActual_vertex2 R S) (map13_left R S) (map13_right R S)
  simp only [OriginalGeometricTriple318.Cocycle,OriginalGeometricTriple318.edge12,
    OriginalGeometricTriple318.edge23,OriginalGeometricTriple318.edge13]
  rw [← h01, ← h12, ← h02, SheafPathTransport318.composition, hτ]

/-- The actual diagonal identity becomes the normalized tensor diagonal
identity before any module/coaction conversion. -/
lemma normalized_diagonal (hτ : ActualAffineSheafData318.Diagonal R S L τ) :
    SheafPathTransport318.transport L.object (Spec.map (AffineOverlapDiagonal318.diagonal R S))
      (Spec.map (leftMap R S S)) (Spec.map (rightMap R S S)) (Spec.map (𝟙 S)) (Spec.map (𝟙 S))
      (spec_path _ _ _ (AffineOverlapDiagonal318.diagonal_left R S))
      (spec_path _ _ _ (AffineOverlapDiagonal318.diagonal_right R S))
      (overlap R S L τ) = 𝟙 _ := by
  have hs : (𝟙 (Spec S)) ≫ ActualOverlapDiagram318.diagonal (baseMap R S) =
      Spec.map (AffineOverlapDiagonal318.diagonal R S) ≫ (doubleIso R S).inv := by
    simpa only [Category.id_comp] using ActualAffineDoubleNerve318.diagonal R S
  have h := SheafPathTransport318.square L.object
    (ActualOverlapDiagram318.diagonal (baseMap R S)) (𝟙 (Spec S))
    (doubleIso R S).inv (Spec.map (AffineOverlapDiagonal318.diagonal R S)) hs
    (ActualOverlapDiagram318.first (baseMap R S)) (ActualOverlapDiagram318.second (baseMap R S))
    (Spec.map (𝟙 S)) (Spec.map (𝟙 S))
    (Spec.map (leftMap R S S)) (Spec.map (rightMap R S S)) (Spec.map (𝟙 S)) (Spec.map (𝟙 S))
    ((ActualOverlapDiagram318.diagonal_first (baseMap R S)).trans (Spec.map_id S).symm)
    ((ActualOverlapDiagram318.diagonal_second (baseMap R S)).trans (Spec.map_id S).symm)
    (inverse_first R S) (inverse_second R S) (Category.id_comp _) (Category.id_comp _)
    (spec_path _ _ _ (AffineOverlapDiagonal318.diagonal_left R S))
    (spec_path _ _ _ (AffineOverlapDiagonal318.diagonal_right R S)) τ
  rw [hτ, SheafPathTransport318.identity] at h
  exact h.symm

/-- Canonical normalization is cancelled, and the original identity
comparison is restored, giving precisely the geometric diagonal equation
consumed by the existing affine reconstruction. -/
lemma diagonal (hτ : ActualAffineSheafData318.Diagonal R S L τ) :
    OriginalGeometricDiagonal318.Diagonal R S L (overlap R S L τ) := by
  let d₀ := PullbackPathComposition318.iso
    (Spec.map (AffineOverlapDiagonal318.diagonal R S)) (Spec.map (leftMap R S S)) (Spec.map (𝟙 S))
    (spec_path _ _ _ (AffineOverlapDiagonal318.diagonal_left R S))
  let j := (TildePullbackIdentity318.pullbackId S).app L.object
  have h := congrArg (fun k => d₀.hom.app L.object ≫ k ≫ j.hom)
    (normalized_diagonal R S L τ hτ)
  simpa only [SheafPathTransport318.transport, OriginalGeometricDiagonal318.Diagonal,
    OriginalGeometricDiagonal318.firstComparison, OriginalGeometricDiagonal318.secondComparison,
    OriginalGeometricDiagonal318.splitSheaf, OriginalGeometricDiagonal318.diagonal,
    affine_path, Iso.trans_hom, Iso.app_hom, Category.assoc,
    Iso.hom_inv_id_app_assoc, Category.id_comp, Category.comp_id, d₀, j] using h
end ActualAffineTensorLaws318
