module
public import OpenSchemeTransition318
public import OpenChartLineEffectivity318
public section
noncomputable section
namespace OpenSchemeGluing318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenSheafRestrictionCompatibility318 OpenChartModuleImages318 OpenSchemeTransition318
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} {M : ι → X.Modules}
  (D : OpenSchemeTransition318.Data U M)
abbrev sheaf := OpenSheafGluing318.sheaf (OpenSchemeTransition318.overData D)
abbrev comparison (i : ι) := OpenSheafGluing318.chartIso (OpenSchemeTransition318.overData D) i

lemma comparison_toOver (i : ι) : toOverIso (U i) (comparison D i) =
    OpenSheafGluing318.overIso (OpenSchemeTransition318.overData D) i := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv (U i)).functor.map_injective
  rw [OpenSheafRestrictionCompatibility318.map_toOver_hom]
  simp only [comparison, OpenSheafGluing318.chartIso, OpenModuleGluedSheaf318.chartIso,
    Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Recovered actual open-subscheme comparisons realize exactly the
original scheme-local sheaf transition on the original pair intersection. -/
lemma transition_recovered (i j : ι) :
    schemeRestrict (comparison D i) (show U i ⊓ U j ≤ U i from inf_le_left) ≪≫ D.transition i j =
      schemeRestrict (comparison D j) (show U i ⊓ U j ≤ U j from inf_le_right) := by
  apply toOver_injective
  rw [toOver_trans, restriction_compatible, restriction_compatible,
    comparison_toOver, comparison_toOver]
  exact OpenSheafGluing318.transition_recovered (OpenSchemeTransition318.overData D) i j

/-- Original scheme-local sheaf data is effective, with the exact original
restriction-normalized compatibility square. The over-open/scalar laws have
been derived, not restated as assumptions. -/
theorem effective : ∃ (G : X.Modules)
    (e : ∀ i, G.restrict (U i).ι ≅ (M i).restrict (U i).ι),
    ∀ i j,
      schemeRestrict (e i) (show U i ⊓ U j ≤ U i from inf_le_left) ≪≫ D.transition i j =
        schemeRestrict (e j) (show U i ⊓ U j ≤ U j from inf_le_right) :=
  ⟨sheaf D, comparison D, transition_recovered D⟩

variable (L : ∀ i, LineSheafClass318.Line (U i).toScheme)
  (E : OpenSchemeTransition318.Data U
    (OpenChartModuleImages318.ambient U (fun i => (L i).object)))

/-- The complete original scheme-local ambient datum glues arbitrary local
lines. Original actual scheme triple laws supply all over-open gluing laws;
the original full local frame covers supply genuine global rank-one frames. -/
@[expose] def line (hcover : (⊤ : X.Opens) ≤ iSup U) : LineSheafClass318.Line X :=
  OpenChartLineEffectivity318.line U L (OpenSchemeTransition318.overData E) hcover

@[expose] def lineComparison (hcover : (⊤ : X.Opens) ≤ iSup U) (i : ι) :
    (line L E hcover).object.restrict (U i).ι ≅ (L i).object :=
  OpenChartLineEffectivity318.comparison U L (OpenSchemeTransition318.overData E) hcover i
end OpenSchemeGluing318
