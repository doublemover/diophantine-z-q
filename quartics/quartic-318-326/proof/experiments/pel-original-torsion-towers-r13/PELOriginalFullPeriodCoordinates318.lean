module
public import PELOriginalOrderCoverInverse318
public import LatticeQuotientKernel318
public section
noncomputable section
namespace PELOriginalFullPeriodCoordinates318
open QuaternionicRealPeriod318 QuaternionicOrderPeriodQuotient318
open PELPrincipalOrderCoordinates318 PELQuaternionRealRepresentation318
variable (τ : ℂ) (hτ : 0 < τ.im)
abbrev Periods := periodSubgroup representation order τ
@[expose] def map : Coordinates →+ Periods τ where
  toFun x := ⟨periodHom representation τ (embed x),⟨embed x,⟨x,rfl⟩,rfl⟩⟩
  map_zero' := Subtype.ext (by rw [embed_zero,map_zero])
  map_add' x y := Subtype.ext (by rw [embed_add,map_add])
include hτ in
lemma bijective : Function.Bijective (map τ) := by
  constructor
  · intro x y h
    apply embed_injective
    apply representation_injective
    apply (periodEquiv τ hτ).injective
    exact congrArg Subtype.val h
  · rintro ⟨z,b,hb,hbz⟩
    obtain ⟨x,rfl⟩ := hb
    exact ⟨x,Subtype.ext hbz⟩
@[expose] def equivalence : Coordinates ≃+ Periods τ := AddEquiv.ofBijective (map τ) (bijective τ hτ)
lemma action_square (a : order) (ha : PELOriginalOrderIntegralNorm318.norm a≠0) (x : Coordinates) :
    equivalence τ hτ (PELOriginalOrderLatticeMatrix318.action a x)=
      LatticeQuotientKernel318.lattice (Periods τ)
        (PELOriginalOrderCoverInverse318.equivalence a ha).toAddEquiv
        (order_preserves_periods representation order τ a) (equivalence τ hτ x) := by
  apply Subtype.ext
  change periodHom representation τ (embed (PELOriginalOrderLatticeMatrix318.action a x))=
    leftLinear (representation a) (periodHom representation τ (embed x))
  rw [←periodHom_mul]
  apply congrArg (periodHom representation τ)
  exact congrArg Subtype.val (PELOriginalOrderLatticeMatrix318.action_coordinates a x)
end PELOriginalFullPeriodCoordinates318
