module
public import ActualAffineEffectiveComparison318
public section
noncomputable section
namespace CanonicalActualDescentLaws318
open AlgebraicGeometry CategoryTheory
open CanonicalSheafOverlap318 ActualOverlapDiagram318
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {B U D : Scheme.{u}} (M : B.Modules) (f : U ⟶ B)

lemma reflexive (p : D ⟶ U) (b : D ⟶ B) (h : p ≫ f = b) :
    overlap M f p p b h h = 𝟙 _ := by
  exact (PullbackPathComposition318.iso p f b h).hom_inv_id_app M

lemma transitive (p₀ p₁ p₂ : D ⟶ U) (b : D ⟶ B)
    (h₀ : p₀ ≫ f = b) (h₁ : p₁ ≫ f = b) (h₂ : p₂ ≫ f = b) :
    overlap M f p₀ p₁ b h₀ h₁ ≫ overlap M f p₁ p₂ b h₁ h₂ =
      overlap M f p₀ p₂ b h₀ h₂ := by
  simp only [overlap, Category.assoc, Iso.inv_hom_id_app_assoc]

lemma vertex1_path : vertex1 f ≫ f = vertex0 f ≫ f := by
  change (pair01 f ≫ second f) ≫ f = (pair01 f ≫ first f) ≫ f
  rw [Category.assoc, Category.assoc, edge_condition]

lemma vertex2_path : vertex2 f ≫ f = vertex0 f ≫ f := (outer_condition f).symm

lemma pair12_path : pair12 f ≫ (first f ≫ f) = vertex0 f ≫ f := by
  rw [← Category.assoc, ← middle_condition]
  exact vertex1_path f

lemma pair02_path : pair02 f ≫ (first f ≫ f) = vertex0 f ≫ f := by
  rw [← Category.assoc, pair02_first]

lemma diagonal_path : diagonal f ≫ (first f ≫ f) = f := by
  rw [← Category.assoc, diagonal_first, Category.id_comp]

/-- The actual categorical triple cocycle of every original pulled-back
module sheaf follows from path composition and inverse cancellation. -/
lemma triple :
    SheafPathTransport318.transport ((Scheme.Modules.pullback f).obj M) (pair01 f)
      (first f) (second f) (vertex0 f) (vertex1 f) rfl rfl (actual M f) ≫
    SheafPathTransport318.transport ((Scheme.Modules.pullback f).obj M) (pair12 f)
      (first f) (second f) (vertex1 f) (vertex2 f) (middle_condition f).symm rfl (actual M f) =
    SheafPathTransport318.transport ((Scheme.Modules.pullback f).obj M) (pair02 f)
      (first f) (second f) (vertex0 f) (vertex2 f) (pair02_first f) (pair02_second f) (actual M f) := by
  simp only [actual]
  rw [CanonicalSheafOverlap318.transport M f (pair01 f) (first f) (second f)
    (first f ≫ f) rfl (edge_condition f).symm (vertex0 f) (vertex1 f)
    (vertex0 f ≫ f) rfl rfl rfl (vertex1_path f) (Category.assoc _ _ _).symm]
  rw [CanonicalSheafOverlap318.transport M f (pair12 f) (first f) (second f)
    (first f ≫ f) rfl (edge_condition f).symm (vertex1 f) (vertex2 f)
    (vertex0 f ≫ f) (middle_condition f).symm rfl (vertex1_path f) (vertex2_path f) (pair12_path f)]
  rw [CanonicalSheafOverlap318.transport M f (pair02 f) (first f) (second f)
    (first f ≫ f) rfl (edge_condition f).symm (vertex0 f) (vertex2 f)
    (vertex0 f ≫ f) (pair02_first f) (pair02_second f) rfl (vertex2_path f) (pair02_path f)]
  exact transitive M f _ _ _ _ _ _ _

/-- The original diagonal law holds for any named identity map, with its
actual equality transport retained at both endpoints. -/
lemma diagonal_identity (v : U ⟶ U) (hv : 𝟙 U = v) :
    SheafPathTransport318.transport ((Scheme.Modules.pullback f).obj M) (diagonal f)
      (first f) (second f) v v ((diagonal_first f).trans hv) ((diagonal_second f).trans hv)
      (actual M f) = 𝟙 _ := by
  simp only [actual]
  have hp : v ≫ f = f := by rw [← hv, Category.id_comp]
  rw [CanonicalSheafOverlap318.transport M f (diagonal f) (first f) (second f)
    (first f ≫ f) rfl (edge_condition f).symm v v f
    ((diagonal_first f).trans hv) ((diagonal_second f).trans hv) hp hp (diagonal_path f)]
  exact reflexive M f v f hp
end CanonicalActualDescentLaws318
