module
public import PELOriginalOpenRegularFunction318
public import PELOriginalPolarizationAutomorphy318
public section
noncomputable section
namespace PELOriginalOpenRegularNaturality318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalPolarizationAutomorphy318 PELOriginalChartAnalyticEvaluation318
open PELOriginalOpenRegularFunction318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- The evaluation is the genuine structural ring homomorphism. Thus
whole overlap identities and units specialize without a new scalar action. -/
@[expose] def evaluation (U : (candidate τ hτ).Opens) (z : ComplexVectors)
    (hz : z∈domain τ hτ U) : Γ(candidate τ hτ,U) →+* ℂ :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom.comp (point τ hτ U z hz).appTop.hom).comp
    (LineFrameTopScalar318.ringTop U).inv.hom

lemma value_eq_evaluation (U : (candidate τ hτ).Opens) (s : Γ(candidate τ hτ,U))
    (z : ComplexVectors) (hz : z∈domain τ hτ U) :
    value τ hτ U s z=evaluation τ hτ U z hz s := by
  rw [value,dif_pos hz]
  rfl

lemma domain_period (U : (candidate τ hτ).Opens) (l : L τ hτ) (z : ComplexVectors) :
    z+l.val∈domain τ hτ U ↔ z∈domain τ hτ U := by
  simp only [domain,Set.mem_setOf_eq,projection_add_period]

/-- The original lattice acts trivially on actual regular-function
values, including the harmless total extensions outside the open. -/
theorem value_period (U : (candidate τ hτ).Opens) (s : Γ(candidate τ hτ,U))
    (l : L τ hτ) (z : ComplexVectors) : value τ hτ U s (z+l.val)=value τ hτ U s z := by
  by_cases hz : z∈domain τ hτ U
  · have hzl := (domain_period τ hτ U l z).mpr hz
    have hp : point τ hτ U (z+l.val) hzl=point τ hτ U z hz := by
      apply (cancel_mono U.ι).1
      rw [point_ι,point_ι,projection_add_period]
    rw [value,dif_pos hzl,value,dif_pos hz,hp]
  · have hzl := mt (domain_period τ hτ U l z).mp hz
    simp only [value,dif_neg hz,dif_neg hzl]

/-- Actual original-open restriction commutes with original analytic
specialization on every smaller open. -/
theorem value_restrict (U W : (candidate τ hτ).Opens) (h : W≤U)
    (s : Γ(candidate τ hτ,U)) (z : ComplexVectors) (hz : z∈domain τ hτ W) :
    value τ hτ W ((candidate τ hτ).presheaf.map (homOfLE h).op s) z=value τ hτ U s z := by
  let q := point τ hτ W z hz
  have hp : (q≫(candidate τ hτ).homOfLE h)≫U.ι=
      candidateComplexPoint τ hτ (projection (P τ) z) := by
    rw [Category.assoc,Scheme.homOfLE_ι]
    exact point_ι τ hτ W z hz
  rw [value_at_point τ hτ U s z _ hp,value_eq_evaluation τ hτ W _ z hz]
  change (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (q.appTop
      ((LineFrameTopScalar318.ringTop W).inv
        ((candidate τ hτ).presheaf.map (homOfLE h).op s)))=_
  have he := OriginalOpenCoefficientSpecialization318.coefficient_pullback U W h
    ((LineFrameTopScalar318.ringTop U).inv s)
  simp only [GlobalSectionFrameCoordinates318.coefficient,Iso.inv_hom_id_apply] at he
  rw [he]
  rfl

/-- The exact pullback specialization for ANY actual candidate morphism
with its proved original-cover action, in particular every translation.
No analyticity of the map or chosen inverse chart is assumed here. -/
theorem value_pullback (f : candidate τ hτ ⟶ candidate τ hτ) (φ : ComplexVectors → ComplexVectors)
    (hf : ∀ z,candidateComplexPoint τ hτ (projection (P τ) z)≫f=
      candidateComplexPoint τ hτ (projection (P τ) (φ z)))
    (U : (candidate τ hτ).Opens) (s : Γ(candidate τ hτ,U))
    (z : ComplexVectors) (hz : z∈domain τ hτ (f ⁻¹ᵁ U)) :
    value τ hτ (f ⁻¹ᵁ U) (f.app U s) z=value τ hτ U s (φ z) := by
  have hφ : φ z∈domain τ hτ U := by
    change candidateComplexPoint τ hτ (projection (P τ) (φ z)) (IsLocalRing.closedPoint ℂ)∈U
    rw [←hf z,Scheme.Hom.comp_apply]
    exact hz
  rw [value_at_point τ hτ (f ⁻¹ᵁ U) _ z _ (point_ι τ hτ (f ⁻¹ᵁ U) z hz),
    value_at_point τ hτ U s (φ z) _ (point_ι τ hτ U (φ z) hφ)]
  symm
  apply OpenPointScalarPullback318.evaluation_pullback f U s
  rw [←Category.assoc,point_ι,point_ι,hf]
end PELOriginalOpenRegularNaturality318
