module
public import RegularClosedIso318
public section
noncomputable section
namespace RegularClosedSquareIso318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {Z W X Y : Scheme.{u}} (p : Z ⟶ X) (q : W ⟶ Y)
  (d : Z ≅ W) (e : X ≅ Y) (he : d.hom ≫ q=p ≫ e.hom)
include he in
/-- Both source AND target isomorphisms transport the literal quotient
charts and their equations, preserving the whole Cartier condition. -/
lemma transport (h : OriginalRegularClosedCharts318.Property p) :
    OriginalRegularClosedCharts318.Property q := by
  intro x
  obtain ⟨A,j,hj,⟨v,hv⟩,c,z,H,hc⟩ := h (e.inv x)
  letI : IsOpenImmersion j := hj
  refine ⟨A,j ≫ e.hom,inferInstance,⟨v,?_⟩,c,z ≫ d.hom,?_,hc⟩
  · rw [Scheme.Hom.comp_apply,hv,← Scheme.Hom.comp_apply,e.inv_hom_id]
    rfl
  · apply H.of_iso (Iso.refl _) (Iso.refl _) d e
    · simp only [Iso.refl_hom,Category.id_comp,Category.comp_id]
    · simp only [Iso.refl_hom,Category.id_comp]
    · simp only [Iso.refl_hom,Category.id_comp]
    · exact he.symm
end RegularClosedSquareIso318
