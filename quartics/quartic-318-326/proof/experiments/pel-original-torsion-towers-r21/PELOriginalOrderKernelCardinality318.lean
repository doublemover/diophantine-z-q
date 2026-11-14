module
public import PELOriginalOrderKernelLatticeQuotient318
public section
noncomputable section
namespace PELOriginalOrderKernelCardinality318
open PELPrincipalOrderCoordinates318 PELOriginalOrderIntegralNorm318
open PELOriginalOrderLatticeMatrix318 PELOriginalOrderKernelLatticeQuotient318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order) (ha : norm a≠0)
include ha in
/-- The determinant computes the quotient of the FULL original integral
coordinate module by the actual left-multiplication image. -/
lemma lattice_card : Nat.card (Coordinates ⧸ (action a).range)=(norm a).natAbs^2 := by
  have he := Submodule.natAbs_det_equiv (action a).range
    (LinearEquiv.ofInjective (action a) (action_injective a ha))
  change (LinearMap.det (action a)).natAbs=Nat.card (Coordinates ⧸ (action a).range) at he
  rw [action,LinearMap.det_toLin',determinant,Int.natAbs_pow] at he
  exact he.symm
include hτ ha in
/-- Exact cardinality of the actual original torus kernel. This is
obtained through a literal lattice quotient, not a degree convention. -/
lemma torus_card : Nat.card (TorusKernel τ a)=(norm a).natAbs^2 := by
  rw [←Nat.card_congr (quotientEquiv τ hτ a ha).toEquiv]
  exact lattice_card a ha
end PELOriginalOrderKernelCardinality318
