module
public import OriginalGeometricEdge318
public import OriginalLineOverlapCoaction318
public import AffineTripleOverlapMaps318
public section
noncomputable section
namespace OriginalGeometricTriple318
open AlgebraicGeometry CategoryTheory LineSheafClass318 AffineModuleBaseChange318
open AffineCechRings318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (L : Line (Spec S))
  (τ : OriginalLineOverlapCoaction318.first R S L ⟶
    OriginalLineOverlapCoaction318.second R S L)

abbrev edge12 := OriginalGeometricEdge318.edge L (leftMap R S S) (rightMap R S S)
  (map12 R S) (vertex1 R S) (vertex2 R S) (map12_left R S) (map12_right R S) τ
abbrev edge13 := OriginalGeometricEdge318.edge L (leftMap R S S) (rightMap R S S)
  (map13 R S) (vertex1 R S) (vertex3 R S) (map13_left R S) (map13_right R S) τ
abbrev edge23 := OriginalGeometricEdge318.edge L (leftMap R S S) (rightMap R S S)
  (map23 R S) (vertex2 R S) (vertex3 R S) (map23_left R S) (map23_right R S) τ

/-- The actual module-sheaf cocycle on the spectrum of the full triple
tensor ring, using the original canonical pullback path comparisons. -/
@[expose] def Cocycle : Prop :=
  edge12 R S L τ ≫ edge23 R S L τ = edge13 R S L τ

lemma overlap_map : OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ =
    AffineSectionConjugation318.morphism L (leftMap R S S) (rightMap R S S) τ :=
  OriginalLineOverlapCoaction318.moduleHomEquiv_apply R S L τ

lemma edge12_to_module :
    AffineSectionConjugation318.morphism L (vertex1 R S) (vertex2 R S) (edge12 R S L τ) =
      AffineTripleOverlapMaps318.edge12 R S (OriginalLineAffineModel318.sections S L)
        (OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ) := by
  rw [overlap_map]
  exact OriginalGeometricEdge318.edge_to_module _ _ _ _ _ _ _ _ _
lemma edge13_to_module :
    AffineSectionConjugation318.morphism L (vertex1 R S) (vertex3 R S) (edge13 R S L τ) =
      AffineTripleOverlapMaps318.edge13 R S (OriginalLineAffineModel318.sections S L)
        (OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ) := by
  rw [overlap_map]
  exact OriginalGeometricEdge318.edge_to_module _ _ _ _ _ _ _ _ _
lemma edge23_to_module :
    AffineSectionConjugation318.morphism L (vertex2 R S) (vertex3 R S) (edge23 R S L τ) =
      AffineTripleOverlapMaps318.edge23 R S (OriginalLineAffineModel318.sections S L)
        (OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ) := by
  rw [overlap_map]
  exact OriginalGeometricEdge318.edge_to_module _ _ _ _ _ _ _ _ _

/-- Genuine geometric triple overlap coherence implies the exact original
module cocycle consumed by the coassociativity proof. -/
lemma cocycle_to_module (hτ : Cocycle R S L τ) :
    AffineTripleOverlapMaps318.Cocycle R S (OriginalLineAffineModel318.sections S L)
      (OriginalLineOverlapCoaction318.moduleHomEquiv R S L τ) := by
  change _ ≫ _ = _
  rw [← edge12_to_module, ← edge23_to_module, ← edge13_to_module,
    AffineSectionConjugation318.morphism_comp, hτ]
end OriginalGeometricTriple318
