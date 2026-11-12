module
public import PELOriginalFiniteOpenComplexPoints318
public section
noncomputable section
namespace PELOriginalFiniteOpenPointEvaluations318
open AlgebraicGeometry CategoryTheory
open QuaternionicRealPeriod318 PELOriginalLevelTheta318
open PELOriginalProjectedFiniteOpen318 PELOriginalCandidateAffineCharts318
open PELOriginalChartSectionField318 PELOriginalProjectedChartIndependence318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)

/-- The actual Scheme lift is an honest C-algebra evaluation on the
whole localized chart, with BOTH original projected coordinates equal
to the requested vector. This is not an evaluation on a chosen field
component or on a replacement polynomial presentation. -/
theorem exists_evaluation (x : ComplexVectors)
    (hx : value τ hτ 3 j x ≠ 0) (p : BasePolynomial)
    (hf : (Localization.awayMap (polynomialMap τ hτ j x).toRingHom p).Finite)
    (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v p ≠ 0) :
    ∃ e : Localization.Away (polynomialMap τ hτ j x p) →ₐ[ℂ] ℂ,
      e.toRingHom.comp (Localization.awayMap (polynomialMap τ hτ j x).toRingHom p) =
        ComplexPolynomialOpenPoints318.evaluation p v hv ∧
      (∀ k : Fin 2, e (algebraMap (CoordinateChart τ hτ j) _
        (projectedFunction τ hτ x j k)) = v k) ∧
      Spec.map (CommRingCat.ofHom e.toRingHom) ≫ localizedChart τ hτ j x p ≫
        PELOriginalProperComplexCandidate318.structureMap τ hτ = 𝟙 _ := by
  obtain ⟨q,hq,hC⟩ := PELOriginalFiniteOpenComplexPoints318.exists_localized_point
    τ hτ j x hx p hf v hv
  obtain ⟨φ,rfl⟩ := Spec.map_surjective q
  have hscalar := hC
  rw [PELOriginalFiniteOpenBaseChange318.original_complex_base] at hscalar
  have heC : CommRingCat.ofHom (algebraMap ℂ
      (Localization.Away (polynomialMap τ hτ j x p))) ≫ φ = 𝟙 _ := by
    apply Spec.map_injective
    rw [Spec.map_comp,Spec.map_id]
    exact hscalar
  let e : Localization.Away (polynomialMap τ hτ j x p) →ₐ[ℂ] ℂ :=
    { φ.hom with commutes' := fun c => congrArg (fun f => f.hom c) heC }
  have heP : CommRingCat.ofHom
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom p) ≫ φ =
      CommRingCat.ofHom (ComplexPolynomialOpenPoints318.evaluation p v hv) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    exact hq
  have he : e.toRingHom.comp
      (Localization.awayMap (polynomialMap τ hτ j x).toRingHom p) =
        ComplexPolynomialOpenPoints318.evaluation p v hv := congrArg (fun f => f.hom) heP
  refine ⟨e,he,?_,hC⟩
  intro k
  have h := congrArg (fun f : Localization.Away p →+* ℂ =>
      f (algebraMap BasePolynomial (Localization.Away p) (MvPolynomial.X k))) he
  simpa only [RingHom.comp_apply,Localization.awayMap,IsLocalization.Away.map,
    IsLocalization.map_eq,polynomialMap_X,ComplexPolynomialOpenPoints318.evaluation_source,
    MvPolynomial.eval_X] using h
end PELOriginalFiniteOpenPointEvaluations318
