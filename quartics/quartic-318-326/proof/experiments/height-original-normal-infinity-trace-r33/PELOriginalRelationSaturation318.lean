module
public import PELOriginalRelationKernelIntersection318
public import Mathlib.RingTheory.Ideal.Colon
public section
noncomputable section
namespace PELOriginalRelationSaturation318
open PELOriginalCubicRelationIdeal318 PELOriginalRelationKernelIntersection318
open PELOriginalAllLevelProjectiveMap318 PELOriginalPolarizationTransitions318
open PELOriginalLevelTheta318
attribute [local instance] MvPolynomial.gradedAlgebra
variable (τ:ℂ)(hτ:0<τ.im)
@[expose] def irrelevant:Ideal Equations:=
  (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Label 3) ℂ)).toIdeal
lemma variable_irrelevant(r:Label 3):MvPolynomial.X r∈irrelevant:=
  HomogeneousIdeal.mem_irrelevant_of_mem _ (by norm_num:0<(1:ℕ))
    (MvPolynomial.isHomogeneous_X ℂ r)

/-- Saturation is proved at EVERY actual cone point by selecting one
of the same nine nonvanishing cubic coordinates. No uniform coordinate
or unproved projective-normality statement is used. -/
theorem irrelevant_power_test(p:Equations)(n:ℕ):
    (∀g∈irrelevant^n,p*g∈relations τ hτ)↔p∈relations τ hτ:=by
  constructor
  · intro h
    apply (relation_iff_all_point_kernels τ hτ p).mpr
    intro q
    obtain ⟨r,hr⟩:=coordinate_nonzero τ hτ q
    have hg:(MvPolynomial.X r:Equations)^n∈irrelevant^n:=
      Ideal.pow_mem_pow (variable_irrelevant r) n
    have hh: p*(MvPolynomial.X r)^n∈pointKernel τ hτ q:=
      (relation_iff_all_point_kernels τ hτ _).mp (h _ hg) q
    let v:=baseVector τ hτ 1 q
    have hx:ComplexProjectiveMarkerPoint318.marker v (MvPolynomial.X r)≠0:=by
      intro hz
      have hm:MvPolynomial.X r∈ComplexProjectiveMarkerPoint318.kernel v:=hz
      exact hr ((ComplexProjectiveMarkerPoint318.variable_mem_iff v r).mp hm)
    change ComplexProjectiveMarkerPoint318.marker v (p*MvPolynomial.X r^n)=0 at hh
    rw [map_mul,map_pow] at hh
    exact (mul_eq_zero.mp hh).resolve_right (pow_ne_zero n hx)
  · intro hp g hg
    exact (relations τ hτ).mul_mem_right g hp

/-- Exact colon equality for every power of the actual irrelevant
ideal; hence the whole irrelevant-power saturation changes NOTHING. -/
theorem colon_power_eq(n:ℕ):
    (relations τ hτ).colon (irrelevant^n:Set Equations)=relations τ hτ:=by
  ext p
  rw [Submodule.mem_colon]
  simpa only [smul_eq_mul] using irrelevant_power_test τ hτ p n

theorem saturation_membership(p:Equations):
    (∃n:ℕ,∀g∈irrelevant^n,p*g∈relations τ hτ)↔p∈relations τ hτ:=by
  constructor
  · rintro ⟨n,hn⟩
    exact (irrelevant_power_test τ hτ p n).mp hn
  · intro hp
    exact ⟨0,(irrelevant_power_test τ hτ p 0).mpr hp⟩
end PELOriginalRelationSaturation318
