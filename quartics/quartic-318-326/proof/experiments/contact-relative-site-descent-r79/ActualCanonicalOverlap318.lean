module
public import CanonicalSheafOverlap318
public import ReconstructedOverlapCompatibility318
public import ActualAffineLineReconstruction318
public section
noncomputable section
namespace ActualCanonicalOverlap318
open AlgebraicGeometry CategoryTheory LineSheafClass318 AffineModuleBaseChange318
open ActualAffineDoubleNerve318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
/-- Normalize affine path components before substituting the large actual nerve. -/
private lemma affine_overlap {A B C : CommRingCat.{u}}
    (f : A ⟶ B) (g₀ g₁ : B ⟶ C) (h : A ⟶ C)
    (h₀ : g₀.hom.comp f.hom = h.hom) (h₁ : g₁.hom.comp f.hom = h.hom)
    (N : (Spec A).Modules) :
    CanonicalSheafOverlap318.overlap N (Spec.map f)
      (Spec.map g₀) (Spec.map g₁) (Spec.map h)
      (spec_path f g₀ h h₀) (spec_path f g₁ h h₁) =
      (OriginalLineNamedComparison318.pullbackAlong f g₀ h h₀).hom.app N ≫
        (OriginalLineNamedComparison318.pullbackAlong f g₁ h h₁).inv.app N := by
  rw [ActualAffineTensorTransport318.affine_path f g₀ h h₀,
    ActualAffineTensorTransport318.affine_path f g₁ h h₁] <;> rfl

variable (R S : CommRingCat.{u}) [Algebra R S] (M : ModuleCat R)

/-- The actual categorical-double canonical overlap pulls back to exactly
the canonical tensor-spectrum overlap, not an arbitrary isomorphic datum. -/
lemma transport :
    SheafPathTransport318.transport ((Scheme.Modules.pullback (baseMap R S)).obj (tilde M))
      (doubleIso R S).inv (ActualOverlapDiagram318.first (baseMap R S))
      (ActualOverlapDiagram318.second (baseMap R S))
      (Spec.map (leftMap R S S)) (Spec.map (rightMap R S S))
      (inverse_first R S) (inverse_second R S)
      (CanonicalSheafOverlap318.actual (tilde M) (baseMap R S)) =
        CanonicalTildeOverlap318.sheafOverlap R S M := by
  have hl := spec_path (CanonicalTildeOverlap318.ringMap R S) (leftMap R S S)
    (CanonicalScalarOverlap318.base R S) (CanonicalScalarOverlap318.left_path R S)
  have hr := spec_path (CanonicalTildeOverlap318.ringMap R S) (rightMap R S S)
    (CanonicalScalarOverlap318.base R S) (CanonicalScalarOverlap318.right_path R S)
  have hb : (doubleIso R S).inv ≫
      (ActualOverlapDiagram318.first (baseMap R S) ≫ baseMap R S) =
        Spec.map (CanonicalScalarOverlap318.base R S) := by
    rw [← Category.assoc, inverse_first]
    exact hl
  have h := CanonicalSheafOverlap318.transport (tilde M) (baseMap R S)
    (doubleIso R S).inv (ActualOverlapDiagram318.first (baseMap R S))
    (ActualOverlapDiagram318.second (baseMap R S))
    (ActualOverlapDiagram318.first (baseMap R S) ≫ baseMap R S)
    rfl (ActualOverlapDiagram318.edge_condition (baseMap R S)).symm
    (Spec.map (leftMap R S S)) (Spec.map (rightMap R S S))
    (Spec.map (CanonicalScalarOverlap318.base R S))
    (inverse_first R S) (inverse_second R S) hl hr hb
  exact h.trans (affine_overlap (CanonicalTildeOverlap318.ringMap R S)
    (leftMap R S S) (rightMap R S S) (CanonicalScalarOverlap318.base R S)
    (CanonicalScalarOverlap318.left_path R S) (CanonicalScalarOverlap318.right_path R S)
    ((tilde.functor R).obj M))
end ActualCanonicalOverlap318
