module
public import ComplexLineLiftDerivative318
public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.Calculus.MeanValue
public section
noncomputable section
namespace ComplexLineAffineLifts318
open ComplexLineLatticeAtlas318 ComplexLineHolomorphicLift318 ComplexLineLiftDerivative318
open Set Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 3000000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Quotient L)]
local instance : ChartedSpace ℂ (Quotient L) := chartedSpace L
local instance : IsManifold 𝓘(ℂ,ℂ) ω (Quotient L) := complex_manifold L

/-- The entire derivative descends to the ACTUAL compact torus, hence is
bounded on all C. Liouville then forces an affine lift; no affine-lift
classification theorem is an input. -/
theorem entire_lift_affine (f : Quotient L→Quotient L) (F : ℂ→ℂ)
    (hF : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F)
    (hlift : ∀ z,projection L (F z)=f (projection L z)) :
    ∃ a b : ℂ,∀ z,F z=a*z+b := by
  have hD : Differentiable ℂ (deriv F) := fun z =>
    (contMDiffAt_iff_contDiffAt.mp (hF z)).analyticAt.deriv.differentiableAt
  have hb : Bornology.IsBounded (range (deriv F)) := by
    apply (isCompact_range (quotientDerivative_continuous L f F hF hlift)).isBounded.subset
    rintro w ⟨z,rfl⟩
    exact ⟨projection L z,rfl⟩
  obtain ⟨a,ha⟩ := hD.exists_const_forall_eq_of_bounded hb
  have hdF (z : ℂ) : DifferentiableAt ℂ F z :=
    (contMDiffAt_iff_contDiffAt.mp (hF z)).analyticAt.differentiableAt
  have hd (z : ℂ) : HasDerivAt (fun w => F w-a*w) 0 z := by
    have h := (hdF z).hasDerivAt.sub ((hasDerivAt_id z).const_mul a)
    simpa only [ha,mul_one,sub_self] using h
  have hc := is_const_of_deriv_eq_zero (fun z => (hd z).differentiableAt)
    (fun z => (hd z).deriv)
  refine ⟨a,F 0,?_⟩
  intro z
  have he := hc z 0
  simp only [mul_zero,sub_zero] at he
  linear_combination he

/-- Every holomorphic self-map of this compact discrete complex-line
quotient has an actual affine complex lift. The map need not be invertible. -/
theorem holomorphic_affine_lift (f : Quotient L→Quotient L)
    (hf : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω f) :
    ∃ a b : ℂ,∀ z,f (projection L z)=projection L (a*z+b) := by
  obtain ⟨F,hF,hmap⟩ := exists_entire_lift L f hf
  obtain ⟨a,b,hab⟩ := entire_lift_affine L f F hF hmap
  refine ⟨a,b,?_⟩
  intro z
  rw [←hmap z,hab z]
end ComplexLineAffineLifts318
