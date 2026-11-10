module
public import ContactRelativeOpenPresieve318
public section
noncomputable section
namespace ContactRelativeAffinePresieve318
open AlgebraicGeometry CategoryTheory Opposite
open OriginalRelativeSite318 ContactUniversalRigidifiedClass318 ActualOverlapDiagram318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (t : ℚ) {T T' : Scheme} (b : T ⟶ FieldBase t) (b' : T' ⟶ FieldBase t)
  (g : T' ⟶ T) (hg : g ≫ b = b')

/-- The actual relative-site singleton condition on affine test bases.
The compatible-family equation is evaluated at the original scheme double,
not a newly introduced formal equalizer or an assumed site comparison. -/
lemma isSheafFor [IsAffine T] [Flat g] [Surjective g] [LocallyOfFinitePresentation g] :
    Presieve.IsSheafFor (presheaf (q t)) (Presieve.singleton (arrow b b' g hg)) := by
  rw [Presieve.isSheafFor_singleton]
  intro c hc
  apply ContactFppfCechDescent318.matching_unique t b b' g hg c
  exact hc
    (arrow b' (OriginalTestDoubleClassMaps318.db b' g) (first g) rfl)
    (arrow b' (OriginalTestDoubleClassMaps318.db b' g) (second g)
      (OriginalTestDoubleClassMaps318.second_base b b' g hg))
    (by ext; exact edge_condition g)

lemma fpqc_isSheafFor [IsAffine T] [Flat g] [Surjective g] [QuasiCompact g] :
    Presieve.IsSheafFor (presheaf (q t)) (Presieve.singleton (arrow b b' g hg)) := by
  rw [Presieve.isSheafFor_singleton]
  intro c hc
  apply ContactFppfCechDescent318.fpqc_matching_unique t b b' g hg c
  exact hc
    (arrow b' (OriginalTestDoubleClassMaps318.db b' g) (first g) rfl)
    (arrow b' (OriginalTestDoubleClassMaps318.db b' g) (second g)
      (OriginalTestDoubleClassMaps318.second_base b b' g hg))
    (by ext; exact edge_condition g)
end ContactRelativeAffinePresieve318
