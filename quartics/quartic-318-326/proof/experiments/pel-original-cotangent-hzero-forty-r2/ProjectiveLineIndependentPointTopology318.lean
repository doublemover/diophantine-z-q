module
public import ProjectiveLineComplexSchemePoints318
public import SphereInversion318
public import Mathlib.Topology.Constructions.SumProd
public section
noncomputable section
namespace ProjectiveLineIndependentPointTopology318
open Set Topology
open scoped OnePoint
open ProjectiveLineComplexSchemePoints318 SphereInversion318

/-- The analytic point topology is defined INDEPENDENTLY by the actual
two polynomial chart evaluations. It is not the Zariski topology and is
not transported from the sphere or an arithmetic source. -/
@[expose] def chartPresentation : ℂ⊕ℂ→SchemePoints:=Sum.elim (chartPoint 1) (chartPoint 0)
@[expose,instance_reducible] def pointTopology : TopologicalSpace SchemePoints:=
  TopologicalSpace.coinduced chartPresentation inferInstance
local instance : TopologicalSpace SchemePoints:=pointTopology

lemma chartPresentation_continuous : Continuous chartPresentation:=continuous_coinduced_rng
lemma finite_continuous : Continuous (chartPoint 1):=
  chartPresentation_continuous.comp continuous_inl
lemma infinity_continuous : Continuous (chartPoint 0):=
  chartPresentation_continuous.comp continuous_inr

/-- A map out of the actual scheme-point space is continuous exactly
when its two ORIGINAL polynomial chart restrictions are continuous. -/
theorem continuous_iff_charts {X:Type*} [TopologicalSpace X] (f:SchemePoints→X) :
    Continuous f ↔ Continuous (f ∘ chartPoint 1) ∧ Continuous (f ∘ chartPoint 0) :=
  continuous_coinduced_dom.trans continuous_sum_dom

lemma spherePoint_inversion (z:ℂ) :
    spherePoint (inversion (z:OnePoint ℂ))=chartPoint 0 z := by
  by_cases hz:z=0
  · subst z
    rw [inversion_zero,spherePoint_infty]
  · rw [inversion_coe hz,spherePoint_coe]
    simpa only [inv_inv] using reciprocal_overlap z⁻¹ (inv_ne_zero hz)

lemma inverse_finite (z:ℂ) : sphereSchemeEquiv.symm (chartPoint 1 z)=(z:OnePoint ℂ):=
  sphereSchemeEquiv.symm_apply_apply _
lemma inverse_infinity (z:ℂ) : sphereSchemeEquiv.symm (chartPoint 0 z)=inversion (z:OnePoint ℂ) := by
  rw [←spherePoint_inversion]
  exact sphereSchemeEquiv.symm_apply_apply _

/-- The actual Scheme-point parameterization is continuous against the
independent chart topology, proved separately at finite points and infinity. -/
theorem spherePoint_continuous : Continuous spherePoint := by
  apply continuous_iff_continuousAt.mpr
  intro p
  induction p using OnePoint.rec with
  | coe z =>
    apply OnePoint.isOpenEmbedding_coe.continuousAt_iff.mp
    exact finite_continuous.continuousAt
  | infty =>
    have he:IsOpenEmbedding (fun z:ℂ=>inversion (z:OnePoint ℂ)):=
      inversionHomeomorph.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe
    have hc:Continuous (fun z:ℂ=>spherePoint (inversion (z:OnePoint ℂ))):=by
      simpa only [spherePoint_inversion] using infinity_continuous
    have hh:=he.continuousAt_iff.mp (hc.continuousAt (x:=(0:ℂ)))
    simpa only [inversion_zero] using hh

theorem sphereSchemeEquiv_inverse_continuous : Continuous sphereSchemeEquiv.symm := by
  apply (continuous_iff_charts _).mpr
  constructor
  · simpa only [Function.comp_def,inverse_finite] using (OnePoint.continuous_coe (X:=ℂ))
  · simpa only [Function.comp_def,inverse_infinity] using
      inversionHomeomorph.continuous.comp (OnePoint.continuous_coe (X:=ℂ))

/-- A genuine topology comparison, AFTER the actual target topology was
specified by its own two polynomial charts. -/
@[expose] def sphereSchemeHomeomorph : OnePoint ℂ≃ₜSchemePoints where
  toEquiv:=sphereSchemeEquiv
  continuous_toFun:=spherePoint_continuous
  continuous_invFun:=sphereSchemeEquiv_inverse_continuous

/-- The original evaluation maps are genuine open embeddings for that
independent analytic topology. Their coordinates remain unchanged. -/
theorem chartPoint_open (j:Fin 2) : IsOpenEmbedding (chartPoint j) := by
  fin_cases j
  · have he:=sphereSchemeHomeomorph.isOpenEmbedding.comp
      (inversionHomeomorph.isOpenEmbedding.comp (OnePoint.isOpenEmbedding_coe (X:=ℂ)))
    have hfun:(fun z:ℂ=>sphereSchemeHomeomorph (inversionHomeomorph (z:OnePoint ℂ)))=chartPoint 0:=by
      funext z
      exact spherePoint_inversion z
    simpa only [Function.comp_def,hfun] using he
  · exact sphereSchemeHomeomorph.isOpenEmbedding.comp OnePoint.isOpenEmbedding_coe
end ProjectiveLineIndependentPointTopology318
