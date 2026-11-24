module
public import JLineEvaluation318
public section
noncomputable section
namespace OriginalSparseP1Overlap318
open MvPolynomial HomogeneousLocalization AlgebraicGeometry CategoryTheory
attribute [local instance] MvPolynomial.gradedAlgebra
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S:Type u} [CommRing R] [CommRing S] [Algebra R S]

lemma chartEval_polynomial (φ:MvPolynomial (Fin 2) R→ₐ[R]S)
    (j:Fin 2) (hj:IsUnit (φ (X j))) (v:S) (hv:φ (X j)*v=1) :
    JLineEvaluation318.chartEval φ j hj =
      (Polynomial.aeval (φ (X (j.succAbove 0))*v)).comp
        (JLineAtlas318.chartEquiv R j).toAlgHom := by
  have hh : (JLineEvaluation318.chartEval φ j hj).comp
      (JLineAtlas318.chartEquiv R j).symm.toAlgHom =
      Polynomial.aeval (φ (X (j.succAbove 0))*v) := by
    apply Polynomial.algHom_ext
    change (JLineEvaluation318.chartEval φ j hj) ((JLineAtlas318.chartEquiv R j).symm Polynomial.X) = _
    rw [JLineAtlas318.chartEquiv_symm_X]
    simpa [finSuccAboveEquiv] using JLineEvaluation318.chartEval_coordinate φ j hj (finSuccAboveEquiv j 0) v hv
  ext a
  obtain ⟨b,rfl⟩ := (JLineAtlas318.chartEquiv R j).symm.surjective a
  simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply] using AlgHom.congr_fun hh b

/-- Genuine standard-chart overlap on the actual proper projective line:
the two coordinate maps for a unit and its inverse give the same Scheme map. -/
theorem unit_chart_overlap (x:Sˣ) :
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (↑x:S)).toRingHom) ≫
      JLineAtlas318.chart R 1 =
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (↑x⁻¹:S)).toRingHom) ≫
      JLineAtlas318.chart R 0 := by
  let φ : MvPolynomial (Fin 2) R→ₐ[R]S := aeval ![↑x,1]
  have h1 : IsUnit (φ (X 1)) := by simp [φ]
  have h0 : IsUnit (φ (X 0)) := by simp [φ]
  have e1 := chartEval_polynomial φ 1 h1 1 (by simp [φ])
  have e0 := chartEval_polynomial φ 0 h0 (↑x⁻¹) (by simp [φ])
  have e := JLineEvaluation318.chart_compatibility φ.toRingHom (X 1) (X 0)
    h1 h0 (isHomogeneous_X R 1) (isHomogeneous_X R 0) (by omega) (by omega)
  change Spec.map (CommRingCat.ofHom (JLineEvaluation318.chartEval φ 1 h1).toRingHom) ≫ _ =
    Spec.map (CommRingCat.ofHom (JLineEvaluation318.chartEval φ 0 h0).toRingHom) ≫ _ at e
  rw [e1,e0] at e
  simpa [JLineAtlas318.chart,φ,AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
    CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc] using e

end OriginalSparseP1Overlap318
