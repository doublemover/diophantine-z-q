module
public import PELOriginalFullPeriodCoordinates318
public section
noncomputable section
namespace PELOriginalOrderKernelLatticeQuotient318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
open PELOriginalOrderIntegralNorm318 PELOriginalFullPeriodCoordinates318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order) (ha : norm a≠0)
abbrev TorusKernel := (orderEnd representation order τ a).ker
@[expose] def rootHom : Coordinates →+ TorusKernel τ a :=
  (LatticeQuotientKernel318.rootHom (Periods τ)
    (PELOriginalOrderCoverInverse318.equivalence a ha).toAddEquiv
    (order_preserves_periods representation order τ a)).comp (equivalence τ hτ).toAddMonoidHom
lemma surjective : Function.Surjective (rootHom τ hτ a ha) :=
  (LatticeQuotientKernel318.root_surjective (Periods τ)
    (PELOriginalOrderCoverInverse318.equivalence a ha).toAddEquiv
    (order_preserves_periods representation order τ a)).comp (equivalence τ hτ).surjective
lemma kernel_eq : (rootHom τ hτ a ha).ker=
    (PELOriginalOrderLatticeMatrix318.action a).toAddMonoidHom.range := by
  ext x
  change rootHom τ hτ a ha x=0 ↔ ∃ y,PELOriginalOrderLatticeMatrix318.action a y=x
  constructor
  · intro hx
    have hm : equivalence τ hτ x ∈
        (LatticeQuotientKernel318.rootHom (Periods τ)
          (PELOriginalOrderCoverInverse318.equivalence a ha).toAddEquiv
          (order_preserves_periods representation order τ a)).ker := hx
    rw [LatticeQuotientKernel318.root_kernel] at hm
    obtain ⟨l,hl⟩ := hm
    obtain ⟨y,rfl⟩ := (equivalence τ hτ).surjective l
    refine ⟨y,(equivalence τ hτ).injective ?_⟩
    rw [action_square]
    exact hl
  · rintro ⟨y,hy⟩
    have hm : equivalence τ hτ x ∈
        (LatticeQuotientKernel318.lattice (Periods τ)
          (PELOriginalOrderCoverInverse318.equivalence a ha).toAddEquiv
          (order_preserves_periods representation order τ a)).range := by
      refine ⟨equivalence τ hτ y,?_⟩
      rw [←action_square,hy]
    rw [←LatticeQuotientKernel318.root_kernel] at hm
    exact hm
/-- Explicit both-inverse quotient identification of the actual original
torus kernel with its full integral left-multiplication lattice image. -/
@[expose] def quotientEquiv :
    Coordinates ⧸ (PELOriginalOrderLatticeMatrix318.action a).toAddMonoidHom.range ≃+
      TorusKernel τ a :=
  (QuotientAddGroup.quotientAddEquivOfEq (kernel_eq τ hτ a ha).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (rootHom τ hτ a ha) (surjective τ hτ a ha))
end PELOriginalOrderKernelLatticeQuotient318
