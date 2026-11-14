module
public import PELOriginalNormalizationRootSection318
public import FiniteNormalRootLocalInjection318
public import FiniteNormalMinpolySimpleFibers318
public import PELOriginalNormalizationSmoothNeighborhood318
public section
noncomputable section
namespace PELOriginalSeparatingDerivativeNonzero318
open Set Polynomial QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalChartEvaluationRegularity318 PELOriginalFiniteUnramifiedProjection318
open PELOriginalCandidatePointEquivalence318 PELOriginalCandidateElementFunctions318
open PELOriginalCandidateNormalizationLocalInjection318
open PELOriginalProjectedChartIndependence318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

lemma evaluation_base_square
    (g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
    (algebraEvaluation τ hτ z j hz).toRingHom.comp g.toRingHom =
      MvPolynomial.eval (evaluationVector τ hτ j g z) := by
  have h : (algebraEvaluation τ hτ z j hz).comp g =
      MvPolynomial.aeval (evaluationVector τ hτ j g z) := by
    ext k
    change algebraEvaluation τ hτ z j hz (g (MvPolynomial.X k)) =
      evaluate τ hτ j (g (MvPolynomial.X k)) z
    exact (evaluate_on_chart τ hτ j _ z hz).symm
  exact congrArg AlgHom.toRingHom h

/-- The missing pointwise algebraic conclusion: an element separating
an ENTIRE normalization fiber has nonzero actual minimal-polynomial
derivative at an original point where that same finite normalization
has a genuine analytic local inverse. Proper root lifting, not point
bijection alone, excludes a hidden multiple root at the center. -/
theorem derivative_nonzero
    (g : MvPolynomial (Fin 2) ℂ →ₐ[ℂ] CoordinateChart τ hτ j)
    (hg : Function.Injective g) (hf : g.Finite)
    (x : ComplexVectors) (hx : value τ hτ 3 j x ≠ 0)
    (e : OpenPartialHomeomorph ComplexVectors ComplexVectors)
    (he : ∀ y, e y = evaluationVector τ hτ j g y) (hxe : x ∈ e.source)
    (t : CoordinateChart τ hτ j)
    (hsep : Set.InjOn (fun f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ => f t)
      {f | ∀ r : MvPolynomial (Fin 2) ℂ,
        f (g r) = algebraEvaluation τ hτ x j hx (g r)}) :
    algebraEvaluation τ hτ x j hx
      (PELOriginalNormalizationSmoothNeighborhood318.derivativeElement τ hτ j g t) ≠ 0 := by
  let R := MvPolynomial (Fin 2) ℂ
  let A := CoordinateChart τ hτ j
  letI : Algebra R A := g.toAlgebra
  letI : IsScalarTower ℂ R A := IsScalarTower.of_algebraMap_eq (fun c => (g.commutes c).symm)
  letI : IsTorsionFree R A := isTorsionFree_iff_algebraMap_injective.mpr hg
  letI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).mpr hg
  letI : Module.Finite R A := hf
  let Q := minpoly R t
  let π := PELOriginalCandidateNormalizationTopology318.projection τ hτ j 2 g
  let f0 := algebraEvaluation τ hτ x j hx
  let w0 := toLocus τ hτ j f0
  have hbase (w : Locus τ hτ j) (r : R) :
      toPoint τ hτ j w (algebraMap R A r) = MvPolynomial.eval (π w.val) r :=
    congrArg (fun f : R →ₐ[ℂ] ℂ => f r)
      (PELOriginalCandidateNormalizationTopology318.projection_square τ hτ j 2 g w)
  have hcenter : π w0.val = evaluationVector τ hτ j g x := by
    change π (pointVector τ hτ j f0) = _
    rw [pointVector_original τ hτ j x hx]
    exact projection_original τ hτ j g x hx
  have hsep' : Set.InjOn (fun f : A →ₐ[ℂ] ℂ => f t)
      {f | ∀ r : R, f (algebraMap R A r) = MvPolynomial.eval (π w0.val) r} := by
    intro f hff l hll hfl
    apply hsep (fun r => (hff r).trans ?_) (fun r => (hll r).trans ?_) hfl
    all_goals exact (hbase w0 r).symm.trans
      (congrArg (fun f : A →ₐ[ℂ] ℂ => f (g r)) (toPoint_toLocus τ hτ j f0))
  obtain ⟨U,hU,hxU,hinj⟩ := candidate_locally_injective τ hτ j g x hx e he hxe
  obtain ⟨hr0,V,hV,hxV,hVinj⟩ :=
    FiniteNormalRootLocalInjection318.root_projection_locally_injective A
      (coordinateElement τ hτ j)
      (PELOriginalCandidateAffineOpenImage318.candidateLocus τ hτ j)
      (candidateLocus_closed τ hτ j) (toPoint τ hτ j)
      (toPoint_coordinate τ hτ j) (equivalence τ hτ j).symm.surjective
      π (PELOriginalCandidateNormalizationTopology318.projection_continuous τ hτ j 2 g)
      hbase t (elementValue τ hτ j t) (elementValue_continuous τ hτ j t)
      (toPoint_value τ hτ j t) w0 hsep' U hU hxU hinj
  have hQ (z : ComplexVectors) (hz : value τ hτ 3 j z ≠ 0) :
      (Q.map (MvPolynomial.eval (evaluationVector τ hτ j g z))).IsRoot
        (evaluate τ hτ j t z) := by
    have h := congrArg (algebraEvaluation τ hτ z j hz) (minpoly.aeval R t)
    change algebraEvaluation τ hτ z j hz
      (Q.eval₂ g.toRingHom t) = algebraEvaluation τ hτ z j hz 0 at h
    rw [Polynomial.hom_eval₂,evaluation_base_square,map_zero] at h
    simpa only [Polynomial.IsRoot,Polynomial.eval_map,evaluate_on_chart τ hτ j t z hz] using h
  obtain ⟨W,hW,hxW,b,hb,hbx,hbr⟩ :=
    PELOriginalNormalizationRootSection318.exists_root_section τ hτ j g x hx e he hxe t Q hQ
  have hrootpoint : (⟨(evaluationVector τ hτ j g x,b ⟨_,hxW⟩),hbr ⟨_,hxW⟩⟩ :
      MonicRootProjectionOpen318.Roots (fun v => Q.map (MvPolynomial.eval v))) =
      ⟨(π w0.val,elementValue τ hτ j t w0.val),hr0⟩ := by
    apply Subtype.ext
    apply Prod.ext hcenter.symm
    rw [hbx,evaluate_on_chart,pointVector_value]
  have hnonzero := WholeRootOpenSectionSimple318.derivative_ne_zero Q
    (minpoly.monic (IsIntegral.of_finite R t))
    (FiniteNormalMinpolySimpleFibers318.generic_separable R A t)
    W hW b hb hbr ⟨_,hxW⟩ V hV (hrootpoint.symm ▸ hxV) hVinj
  rw [hbx,evaluate_on_chart] at hnonzero
  have heval : f0 (PELOriginalNormalizationSmoothNeighborhood318.derivativeElement τ hτ j g t) =
      (Q.map (MvPolynomial.eval (evaluationVector τ hτ j g x))).derivative.eval (f0 t) := by
    change f0 (Q.derivative.eval₂ g.toRingHom t) = _
    rw [Polynomial.hom_eval₂,evaluation_base_square,Polynomial.derivative_map,Polynomial.eval_map]
  exact fun hz => hnonzero (heval.symm.trans hz)
end PELOriginalSeparatingDerivativeNonzero318
