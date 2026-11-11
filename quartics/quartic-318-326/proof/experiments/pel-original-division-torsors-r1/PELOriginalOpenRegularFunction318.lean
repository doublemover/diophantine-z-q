module
public import OpenPointScalarPullback318
public import PELOriginalChartTangentDerivation318
public import PELOriginalChartSchemePointIdentity318
public section
noncomputable section
namespace PELOriginalOpenRegularFunction318
open AlgebraicGeometry CategoryTheory QuaternionicRealPeriod318 DiscreteComplexPeriodAtlas318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
open PELOriginalCandidateAffineCharts318 PELOriginalCandidateNineChartCover318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318 PELOriginalChartSchemePointIdentity318
open PELOriginalChartTangentDerivation318 Filter Topology Set
variable (τ : ℂ) (hτ : 0 < τ.im)

@[expose] def domain (U : (candidate τ hτ).Opens) : Set ComplexVectors :=
  {z | candidateComplexPoint τ hτ (projection (P τ) z) (IsLocalRing.closedPoint ℂ)∈U}

/-- The literal original Spec(C) point lifted into the specified actual
open. All later values are pullbacks by THIS morphism. -/
@[expose] def point (U : (candidate τ hτ).Opens) (z : ComplexVectors) (hz : z∈domain τ hτ U) :
    Spec (CommRingCat.of ℂ) ⟶ U.toScheme :=
  IsOpenImmersion.lift U.ι (candidateComplexPoint τ hτ (projection (P τ) z)) (by
    rintro _ ⟨x,rfl⟩
    have hx : x=IsLocalRing.closedPoint ℂ := Subsingleton.elim _ _
    subst x
    exact ⟨⟨_,hz⟩,rfl⟩)

lemma point_ι (U : (candidate τ hτ).Opens) (z : ComplexVectors) (hz : z∈domain τ hτ U) :
    point τ hτ U z hz≫U.ι=candidateComplexPoint τ hτ (projection (P τ) z) :=
  IsOpenImmersion.lift_fac _ _ _

/-- Total harmless extension outside the open; assertions of regularity
are only on the independently defined actual original preimage. -/
@[expose] def value (U : (candidate τ hτ).Opens) (s : Γ(candidate τ hτ,U))
    (z : ComplexVectors) : ℂ :=
  if hz : z∈domain τ hτ U then OpenPointScalarPullback318.value U s (point τ hτ U z hz) else 0

lemma value_at_point (U : (candidate τ hτ).Opens) (s : Γ(candidate τ hτ,U))
    (z : ComplexVectors) (p : Spec (CommRingCat.of ℂ) ⟶ U.toScheme)
    (hp : p≫U.ι=candidateComplexPoint τ hτ (projection (P τ) z)) :
    value τ hτ U s z=OpenPointScalarPullback318.value U s p := by
  have hz : z∈domain τ hτ U := by
    change candidateComplexPoint τ hτ (projection (P τ) z) (IsLocalRing.closedPoint ℂ)∈U
    rw [←hp]
    exact (p (IsLocalRing.closedPoint ℂ)).property
  have he : point τ hτ U z hz=p :=
    (cancel_mono U.ι).1 ((point_ι τ hτ U z hz).trans hp.symm)
  rw [value,dif_pos hz,he]

/-- Every arbitrary algebraic open pulls back to a genuine analytic
open of the ORIGINAL complex cover. No Euclidean topology is transported. -/
theorem isOpen_domain (U : (candidate τ hτ).Opens) : IsOpen (domain τ hτ U) := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  obtain ⟨j,hj⟩ := cover_nonzero τ hτ z
  let F := fun w => (nearbyEvaluation τ hτ z j hj w).toRingHom
  let V := chartMap τ hτ j ⁻¹ᵁ U
  have hv : Spec.map (CommRingCat.ofHom (F z)) (IsLocalRing.closedPoint ℂ)∈V := by
    change chartMap τ hτ j (Spec.map (CommRingCat.ofHom (F z)) (IsLocalRing.closedPoint ℂ))∈U
    simpa only [F,nearbyEvaluation_center,←Scheme.Hom.comp_apply,chart_point] using hz
  have he := AffineOpenEvaluationHolomorphy318.eventually_mem F z
    (fun a => (nearbyEvaluation_differentiable τ hτ z j hj a).continuousAt) V hv
  filter_upwards [he,(holomorphic τ hτ 3 j).continuous.continuousAt.eventually_ne hj] with w hw hjw
  change chartMap τ hτ j (Spec.map (CommRingCat.ofHom (F w)) (IsLocalRing.closedPoint ℂ))∈U at hw
  change candidateComplexPoint τ hτ (projection (P τ) w) (IsLocalRing.closedPoint ℂ)∈U
  simpa only [F,nearbyEvaluation,dif_pos hjw,←Scheme.Hom.comp_apply,chart_point] using hw

/-- Holomorphy of EVERY genuine regular function on EVERY algebraic
open of the original candidate, derived from actual local fractions. -/
theorem differentiableAt_value (U : (candidate τ hτ).Opens) (s : Γ(candidate τ hτ,U))
    (z : ComplexVectors) (hz : z∈domain τ hτ U) :
    DifferentiableAt ℂ (value τ hτ U s) z := by
  obtain ⟨j,hj⟩ := cover_nonzero τ hτ z
  let F := fun w => (nearbyEvaluation τ hτ z j hj w).toRingHom
  let V := chartMap τ hτ j ⁻¹ᵁ U
  have hv : Spec.map (CommRingCat.ofHom (F z)) (IsLocalRing.closedPoint ℂ)∈V := by
    change chartMap τ hτ j (Spec.map (CommRingCat.ofHom (F z)) (IsLocalRing.closedPoint ℂ))∈U
    simpa only [F,nearbyEvaluation_center,←Scheme.Hom.comp_apply,chart_point] using hz
  apply AffineOpenEvaluationHolomorphy318.differentiableAt F z
    (nearbyEvaluation_differentiable τ hτ z j hj) V ((chartMap τ hτ j).app U s) hv
  filter_upwards [(holomorphic τ hτ 3 j).continuous.continuousAt.eventually_ne hj] with w hw
  intro q hq
  let p := q≫(chartMap τ hτ j).resLE U V le_rfl
  have hp : p≫U.ι=candidateComplexPoint τ hτ (projection (P τ) w) := by
    rw [p,Category.assoc,Scheme.Hom.resLE_comp_ι,←Category.assoc,hq]
    simpa only [F,nearbyEvaluation,dif_pos hw] using chart_point τ hτ j w hw
  rw [value_at_point τ hτ U s w p hp]
  exact OpenPointScalarPullback318.evaluation_pullback (chartMap τ hτ j) U s q p (by
    rw [p,Category.assoc,Scheme.Hom.resLE_comp_ι])

/-- Invertible regular functions specialize to nowhere-zero scalars on
exactly the actual open, with no extra analytic nonvanishing premise. -/
theorem unit_value_ne_zero (U : (candidate τ hτ).Opens) (u : Γ(candidate τ hτ,U)ˣ)
    (z : ComplexVectors) (hz : z∈domain τ hτ U) : value τ hτ U u.val z≠0 := by
  rw [value,dif_pos hz]
  exact ((u.isUnit.map (LineFrameTopScalar318.ringTop U).inv.hom).map
    (point τ hτ U z hz).appTop.hom |>.map (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom).ne_zero
end PELOriginalOpenRegularFunction318
