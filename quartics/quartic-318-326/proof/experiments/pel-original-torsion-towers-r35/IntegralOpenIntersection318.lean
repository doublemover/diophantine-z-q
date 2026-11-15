module
public import IntegralOpenUnitMonomorphism318
public section
noncomputable section
namespace IntegralOpenIntersection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
variable {X : Scheme} (U V : X.Opens)

/-- The literal intersection square of actual open subschemes, with
both arrows their genuine open inclusion maps. -/
theorem cartesian : IsPullback (X.homOfLE (show U ⊓ V ≤ V from inf_le_right))
    (X.homOfLE (show U ⊓ V ≤ U from inf_le_left)) V.ι U.ι := by
  apply IsOpenImmersion.isPullback
  · simp only [Scheme.homOfLE_ι]
  · ext x
    change (∃ v : V, v.val=x.val) ↔
      ∃ w : U ⊓ V, (⟨w.val,w.property.1⟩ : U)=x
    constructor
    · rintro ⟨v,hv⟩
      exact ⟨⟨x.val,x.property,hv ▸ v.property⟩,rfl⟩
    · rintro ⟨w,rfl⟩
      exact ⟨⟨w.val,w.property.2⟩,rfl⟩

/-- Every two genuine nonempty opens of an integral scheme meet.
This explicitly supplies the nonempty overlap needed for rational
restriction monomorphisms, rather than inferring it for any open. -/
lemma nonempty [IsIntegral X] [Nonempty U] [Nonempty V] : Nonempty (U ⊓ V).toScheme := by
  obtain ⟨x,hx,hv⟩ := nonempty_preirreducible_inter U.isOpen V.isOpen
    (show (U : Set X).Nonempty from ⟨(Classical.choice (inferInstance : Nonempty U)).val,
      (Classical.choice (inferInstance : Nonempty U)).property⟩)
    (show (V : Set X).Nonempty from ⟨(Classical.choice (inferInstance : Nonempty V)).val,
      (Classical.choice (inferInstance : Nonempty V)).property⟩)
  exact ⟨⟨x,hx,hv⟩⟩
end IntegralOpenIntersection318
