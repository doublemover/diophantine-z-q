module
public import OriginalRegularClosedCharts318
public section
noncomputable section
namespace RegularClosedIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z W X : Scheme.{u}} (p : Z ⟶ X) (q : W ⟶ X)
  (e : Z ≅ W) (he : e.hom ≫ q=p)
include he in
/-- Source-preserving isomorphisms transport the SAME regular equations
and actual quotient pullback squares, with the complete target cover. -/
lemma transport (h : OriginalRegularClosedCharts318.Property p) :
    OriginalRegularClosedCharts318.Property q := by
  intro x
  obtain ⟨A,j,hj,hx,c,z,hz,hr⟩ := h x
  refine ⟨A,j,hj,hx,c,z ≫ e.hom,?_,hr⟩
  apply hz.of_iso (Iso.refl _) (Iso.refl _) e (Iso.refl _)
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  · simp only [Iso.refl_hom,Category.id_comp]
  · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
  · simpa only [Iso.refl_hom,Category.comp_id] using he.symm
end RegularClosedIso318
