module
public import ContactOriginalLineHOneFinite318
public section
noncomputable section
namespace ContactWholeChartRestrictionInjective318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open ContactOriginalLineBothCharts318 ContactOriginalWholeRestriction318
open ContactWholeOpenSectionRestriction318 ContactOriginalRestrictionCoordinates318
open ContactOriginalLaurentCoordinates318 ContactOriginalCohomologyCoordinates318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ) (L : Line (ContactProjectiveModel318.model c))

/-- The original finite-chart restriction is injective by its ACTUAL
polynomial basis localization, not by a supplied generic-fiber identification. -/
lemma finite_injective : Function.Injective (finiteRestriction c L) := by
  intro a b h
  have hc := congrArg (coordinates c L) h
  rw [finite_formula,finite_formula] at hc
  apply (Module.finBasis (Polynomial ℚ) (finiteSections c L)).equivFun.injective
  funext i
  apply Polynomial.toLaurent_injective
  exact congrFun hc i

/-- The full original infinity restriction remains injective with its
actual reciprocal polynomial action and original overlap transition. -/
lemma infinity_injective : Function.Injective (infinityRestriction c L) := by
  intro a b h
  have hc := congrArg (coordinates c L) h
  rw [infinity_formula,infinity_formula] at hc
  have hi := (rawTransition c L).injective hc
  apply (Module.finBasis (Polynomial ℚ) (infinitySections c L)).equivFun.injective
  funext i
  apply Polynomial.toLaurent_injective
  apply LaurentPolynomial.invert.injective
  exact congrFun hi i

lemma finite_original_injective : Function.Injective
    (L.object.presheaf.map (homOfLE inf_le_left :
      finiteOpen c ⊓ infinityOpen c ⟶ finiteOpen c).op) := by
  intro a b h
  apply (finiteSectionsEquiv c L).symm.injective
  apply finite_injective c L
  apply (overlapEquiv c L).injective
  rw [ContactOriginalWholeRestriction318.finite_square,
    ContactOriginalWholeRestriction318.finite_square,
    AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]
  exact h

lemma infinity_original_injective : Function.Injective
    (L.object.presheaf.map (homOfLE inf_le_right :
      finiteOpen c ⊓ infinityOpen c ⟶ infinityOpen c).op) := by
  intro a b h
  apply (infinitySectionsEquiv c L).symm.injective
  apply infinity_injective c L
  apply (overlapEquiv c L).injective
  rw [ContactOriginalWholeRestriction318.infinity_square,
    ContactOriginalWholeRestriction318.infinity_square,
    AddEquiv.apply_symm_apply,AddEquiv.apply_symm_apply]
  exact h

/-- Restriction to the genuine full overlap detects original global
sections because BOTH full chart restrictions are detected there and the
original charts cover the complete model. -/
lemma global_injective : Function.Injective (L.object.presheaf.map
    (homOfLE (show finiteOpen c ⊓ infinityOpen c ≤ ⊤ from le_top)).op) := by
  intro s t h
  let U : Fin 2 → (ContactProjectiveModel318.model c).Opens := ![finiteOpen c,infinityOpen c]
  apply TopCat.Sheaf.eq_of_locally_eq'
    (⟨L.object.presheaf,L.object.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat _)
    U ⊤ (fun _ => homOfLE le_top) ?_ s t
  · exact (le_of_eq (cover c).symm).trans (sup_le (le_iSup U 0) (le_iSup U 1))
  · intro i
    fin_cases i
    · change L.object.presheaf.map (homOfLE (show finiteOpen c ≤ ⊤ from le_top)).op s =
        L.object.presheaf.map (homOfLE (show finiteOpen c ≤ ⊤ from le_top)).op t
      apply finite_original_injective c L
      simpa only [← Functor.map_comp_apply] using h
    · change L.object.presheaf.map (homOfLE (show infinityOpen c ≤ ⊤ from le_top)).op s =
        L.object.presheaf.map (homOfLE (show infinityOpen c ≤ ⊤ from le_top)).op t
      apply infinity_original_injective c L
      simpa only [← Functor.map_comp_apply] using h
end ContactWholeChartRestrictionInjective318
