module
public import PELOriginalFiniteSexticGrowth318
public import LocalizedValueResultant318
public import PELOriginalBoundedFractionRegular318
public import PELOriginalWholeNormalizationRootLift318
public section
noncomputable section
namespace PELOriginalSexticNormRegular318
open Polynomial QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidatePointEquivalence318 PELOriginalSexticChartRatios318
open PELOriginalSectionMultiplication318 ComplexPolynomialOpenPoints318
abbrev Base := MvPolynomial (Fin 2) ℂ
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- A polynomial expression of an actual sextic ratio in ANY whole
finite normalization becomes an ACTUAL regular whole-chart element.
The full-root value identity is explicit: every specialized minpoly
root lifts to a whole original point; its actual sextic value has
polynomial growth without poles. The resultant therefore descends to a
monic base equation, and actual whole-chart normality finishes.

This theorem does not assume a polynomial root-value growth estimate,
a norm-equation construction, or integrality of the sought section.
The remaining input is the literal transferred expression and its value
identity at every whole point above the specified base open. -/
theorem exists_regular
    (g : Base →ₐ[ℂ] CoordinateChart τ hτ j) (hg : Function.Injective g) (hf : g.Finite)
    (t : CoordinateChart τ hτ j) (Q : Polynomial Base)
    (hQ : letI := g.toAlgebra; Q=minpoly Base t)
    (d : Base) (hd : d ≠ 0) (H : Polynomial (Localization.Away d))
    (φ : Localization.Away d →+* FractionRing (CoordinateChart τ hτ j))
    (hφ : φ.comp (algebraMap Base (Localization.Away d)) =
      (algebraMap (CoordinateChart τ hτ j) (FractionRing (CoordinateChart τ hτ j))).comp g.toRingHom)
    (s : homogeneous τ hτ 6)
    (hvalues : ∀ (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v d ≠ 0)
      (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ),
      (∀ r, f (g r)=MvPolynomial.eval v r) →
      H.eval₂ (evaluation d v hv) (f t)=candidateRatio τ hτ j s (toLocus τ hτ j f)) :
    ∃ a : CoordinateChart τ hτ j,
      algebraMap (CoordinateChart τ hτ j) (FractionRing (CoordinateChart τ hτ j)) a =
        H.eval₂ φ (algebraMap (CoordinateChart τ hτ j) (FractionRing (CoordinateChart τ hτ j)) t) := by
  classical
  let A := CoordinateChart τ hτ j
  let K := FractionRing A
  letI : Algebra Base A := g.toAlgebra
  letI : IsScalarTower ℂ Base A := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  letI : IsTorsionFree Base A := isTorsionFree_iff_algebraMap_injective.mpr hg
  letI : Module.Finite Base A := hf
  have hm : Q.Monic := by
    rw [hQ]
    exact minpoly.monic (IsIntegral.of_finite Base t)
  let α := algebraMap Base (Localization.Away d)
  let P := Q.map α
  have hmP : P.Monic := hm.map α
  have heval (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
      (evaluation d v hv).comp α=(MvPolynomial.aeval v : Base →ₐ[ℂ] ℂ).toRingHom := by
    ext r
    exact evaluation_source d v hv r
  have hmap (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
      P.map (evaluation d v hv)=Q.map (MvPolynomial.aeval v : Base →ₐ[ℂ] ℂ).toRingHom := by
    rw [P,Polynomial.map_map,heval]
  let X := {q : (Fin 2 → ℂ) × ℂ // MvPolynomial.eval q.1 d ≠ 0 ∧
    (Q.map (MvPolynomial.aeval q.1 : Base →ₐ[ℂ] ℂ).toRingHom).IsRoot q.2}
  have hlift (q : X) : ∃ f : A →ₐ[ℂ] ℂ,
      (∀ r, f (g r)=MvPolynomial.eval q.val.1 r) ∧ f t=q.val.2 := by
    have hz : ((minpoly Base t).map
        (MvPolynomial.aeval q.val.1 : Base →ₐ[ℂ] ℂ).toRingHom).eval q.val.2=0 := by
      rw [←hQ]
      exact q.property.2
    exact FiniteNormalBaseRootPointLift318.exists_evaluation Base A t
      (MvPolynomial.aeval q.val.1) q.val.2 hz
  choose f hbase ht using hlift
  obtain ⟨C,hC,N,hgrowth⟩ := PELOriginalFiniteSexticGrowth318.fiber_growth
    τ hτ j g hf f (fun q : X => q.val.1) hbase s
  let T := LocalizedValueResultant318.normPolynomial d P H
  have hroots (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v d ≠ 0) :
      ∃ r : Fin P.natDegree → ℂ,
        T.map (evaluation d v hv)=∏ i, (Polynomial.X-Polynomial.C (r i)) ∧
        ∀ i, ‖r i‖ ≤ C*(1+‖v‖)^N := by
    obtain ⟨r,hr,hT⟩ := LocalizedValueResultant318.specialized_product d P H hmP v hv
    refine ⟨fun i => H.eval₂ (evaluation d v hv) (r i),hT,?_⟩
    intro i
    let q : X := ⟨(v,r i),hv,by rw [←hmap v hv]; exact hr i⟩
    have he := hvalues v hv (f q) (hbase q)
    rw [ht q] at he
    rw [he]
    exact hgrowth q
  have hβ : P.eval₂ φ (algebraMap A K t)=0 := by
    rw [P,Polynomial.eval₂_map,hφ]
    change Q.eval₂ ((algebraMap A K).comp (algebraMap Base A)) (algebraMap A K t)=0
    rw [←Polynomial.hom_eval₂,hQ,←Polynomial.aeval_def,minpoly.aeval,map_zero]
  exact PELOriginalBoundedFractionRegular318.exists_regular τ hτ j d hd g.toRingHom φ hφ T
    (LocalizedValueResultant318.monic d P H hd hmP) _
    (LocalizedValueResultant318.annihilates d P H φ _ hβ)
    P.natDegree N C hC hroots
end PELOriginalSexticNormRegular318
