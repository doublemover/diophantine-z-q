module
public import PELOriginalFunctionNormRegular318
public import FractionFiniteCoefficientLift318
public import PELOriginalCandidateNormalizationTopology318
public section
noncomputable section
namespace PELOriginalFunctionRegularEvaluation318
open Set Polynomial QuaternionicRealPeriod318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalCandidateAffineCharts318 PELOriginalChartAnalyticEvaluation318
open PELOriginalCandidatePointEquivalence318 PELOriginalPolynomialGrowthFunction318
open PELOriginalSectionMultiplication318 PELOriginalCandidateElementFunctions318
open FractionFiniteCoefficientLift318 ComplexPolynomialOpenPoints318
abbrev Base := MvPolynomial (Fin 2) ℂ
open PELOriginalPolynomialGrowthFunction318
variable (τ : ℂ) (hτ : 0 < τ.im) (j : Label 3)
local instance chartDomain : IsDomain (CoordinateChart τ hτ j) :=
  PELOriginalCandidateChartDomains318.coordinate_chart_domain τ hτ j

/-- A transferred whole-normalization expression gives a regular
section on the ENTIRE original chart, with exact evaluation at EVERY
complex point, including the removed divisor. Integrality is produced
by the literal norm equation; equality on the divisor follows from the
already-proved genuine Euclidean density of the finite projection and
continuity of both actual functions. -/
theorem exists_regular
    (g : Base →ₐ[ℂ] CoordinateChart τ hτ j) (hg : Function.Injective g) (hf : g.Finite)
    (t : CoordinateChart τ hτ j) (d : Base) (hd : d ≠ 0)
    (H : Polynomial (Localization.Away d)) (F : Data τ hτ j)
    (hvalues : ∀ (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v d ≠ 0)
      (f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ),
      (∀ r, f (g r)=MvPolynomial.eval v r) →
      H.eval₂ (evaluation d v hv) (f t)=F.onCandidate (toLocus τ hτ j f)) :
    ∃ a : CoordinateChart τ hτ j, ∀ f : CoordinateChart τ hτ j →ₐ[ℂ] ℂ,
      f a=F.onCandidate (toLocus τ hτ j f) := by
  let A := CoordinateChart τ hτ j
  let K := FractionRing A
  have hgd : g d ≠ 0 := by simpa only [map_zero] using hg.ne hd
  let L := Localization.Away (g.toRingHom d)
  let ψ : L →+* K := toField A K (g.toRingHom d) hgd
  let κ : Localization.Away d →+* L := Localization.awayMap g.toRingHom d
  let φ : Localization.Away d →+* K := ψ.comp κ
  have hκ (r : Base) : κ (algebraMap Base (Localization.Away d) r)=algebraMap A L (g r) := by
    simp only [κ,Localization.awayMap,IsLocalization.Away.map,IsLocalization.map_eq]
    rfl
  have hφ : φ.comp (algebraMap Base (Localization.Away d))=
      (algebraMap A K).comp g.toRingHom := by
    ext r
    change ψ (κ (algebraMap Base (Localization.Away d) r))=algebraMap A K (g r)
    rw [hκ,toField_coefficient]
  letI : Algebra Base A := g.toAlgebra
  obtain ⟨a,ha⟩ := PELOriginalFunctionNormRegular318.exists_regular τ hτ j g hg hf t
    (minpoly Base t) rfl d hd H φ hφ F hvalues
  have hlocal : algebraMap A L a=H.eval₂ κ (algebraMap A L t) := by
    apply toField_injective A K (g.toRingHom d) hgd
    rw [toField_coefficient,Polynomial.hom_eval₂,toField_coefficient]
    exact ha
  have hopen (v : Fin 2 → ℂ) (hv : MvPolynomial.eval v d ≠ 0)
      (f : A →ₐ[ℂ] ℂ) (hfbase : ∀ r, f (g r)=MvPolynomial.eval v r) :
      f a=F.onCandidate (toLocus τ hτ j f) := by
    have hfd : f (g.toRingHom d) ≠ 0 := by
      change f (g d) ≠ 0
      rw [hfbase]
      exact hv
    let E : L →+* ℂ := IsLocalization.Away.lift (g.toRingHom d)
      (g := f.toRingHom) (isUnit_iff_ne_zero.mpr hfd)
    have hE : E.comp κ=evaluation d v hv := by
      apply IsLocalization.ringHom_ext (Submonoid.powers d)
      ext r
      change E (κ (algebraMap Base (Localization.Away d) r))=
        evaluation d v hv (algebraMap Base (Localization.Away d) r)
      rw [hκ,IsLocalization.Away.lift_eq,evaluation_source]
      exact hfbase r
    have he := congrArg E hlocal
    rw [IsLocalization.Away.lift_eq,Polynomial.hom_eval₂,
      IsLocalization.Away.lift_eq,hE] at he
    exact he.trans (hvalues v hv f hfbase)
  let π := PELOriginalCandidateNormalizationTopology318.projection τ hτ j 2 g
  let D : Set (Locus τ hτ j) := {w | MvPolynomial.eval (π w.val) d ≠ 0}
  have hD : Dense D := PELOriginalCandidateNormalizationTopology318.dense_base_open
    τ hτ j 2 g hg hf d hd
  have hc : IsClosed {w : Locus τ hτ j |
      toPoint τ hτ j w a=F.onCandidate w} := by
    have hcont : Continuous (fun w : Locus τ hτ j => toPoint τ hτ j w a) := by
      simpa only [toPoint_value] using
        (elementValue_continuous τ hτ j a).comp continuous_subtype_val
    exact isClosed_eq hcont (F.continuous)
  have hsub : D ⊆ {w : Locus τ hτ j |
      toPoint τ hτ j w a=F.onCandidate w} := by
    intro w hw
    have hsquare (r : Base) : toPoint τ hτ j w (g r)=MvPolynomial.eval (π w.val) r :=
      congrArg (fun f : Base →ₐ[ℂ] ℂ => f r)
        (PELOriginalCandidateNormalizationTopology318.projection_square τ hτ j 2 g w)
    simpa only [toLocus_toPoint] using hopen (π w.val) hw (toPoint τ hτ j w) hsquare
  refine ⟨a,?_⟩
  intro f
  have hw : toLocus τ hτ j f ∈ closure D := by rw [hD.closure_eq]; trivial
  have h := closure_minimal hsub hc hw
  simpa only [mem_setOf_eq,toPoint_toLocus] using h
end PELOriginalFunctionRegularEvaluation318
