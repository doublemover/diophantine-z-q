module
public import JLineEvaluation318
public import OpenJModel318
public section
noncomputable section
namespace JLineOverlap318
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
  have h0 : IsUnit (φ (X 0)) := by simpa [φ] using x.isUnit
  have e1 := chartEval_polynomial φ 1 h1 1 (by simp [φ])
  have e0 := chartEval_polynomial φ 0 h0 (↑x⁻¹) (by simp [φ])
  have e := JLineEvaluation318.chart_compatibility φ.toRingHom (X 1) (X 0)
    h1 h0 (isHomogeneous_X R 1) (isHomogeneous_X R 0) (by omega) (by omega)
  change Spec.map (CommRingCat.ofHom (JLineEvaluation318.chartEval φ 1 h1).toRingHom) ≫ _ =
    Spec.map (CommRingCat.ofHom (JLineEvaluation318.chartEval φ 0 h0).toRingHom) ≫ _ at e
  rw [e1,e0] at e
  simpa [JLineAtlas318.chart,φ,AlgHom.toRingHom_eq_coe, AlgHom.comp_toRingHom,
    CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc] using e

/-- The literal open-j base has the required unit coordinate, so its map to
the proper projective j-line genuinely factors through both standard charts. -/
theorem openJ_chart_overlap (N:ℕ) :
    Spec.map (CommRingCat.ofHom (algebraMap (Polynomial ℤ) (OpenJModel318.Base N))) ≫
      JLineAtlas318.chart ℤ 1 =
    Spec.map (CommRingCat.ofHom
      (Polynomial.aeval (↑((OpenJModel318.base_units N).2.2.2.1.unit)⁻¹:
        OpenJModel318.Base N)).toRingHom) ≫ JLineAtlas318.chart ℤ 0 := by
  convert unit_chart_overlap (R:=ℤ) ((OpenJModel318.base_units N).2.2.2.1.unit) using 1
  congr 2
  apply CommRingCat.hom_ext
  apply Polynomial.ringHom_ext
  · intro z
    simp
  · simp [OpenJModel318.jCoord]

end JLineOverlap318
