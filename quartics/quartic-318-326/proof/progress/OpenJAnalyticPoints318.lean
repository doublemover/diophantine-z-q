module
public import OpenJComplexEvaluation318
public import ShortScaling318
public import PrimitiveTorsion318
public section
noncomputable section
namespace OpenJAnalyticPoints318
open OpenJComplexEvaluation318
set_option maxHeartbeats 0

instance fiber_short (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    (fiber N tau h).IsShortNF := by
  rw [fiber_eq]
  exact ⟨rfl,rfl,rfl⟩

instance analytic_short (tau : UpperHalfPlane) : (ModularWeierstrass318.curve tau).IsShortNF :=
  ⟨rfl,rfl,rfl⟩

theorem exists_scaling (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    ∃ u : ℂˣ, (ModularWeierstrass318.curve tau).a₄ = (u:ℂ)^4 * (fiber N tau h).a₄ ∧
      (ModularWeierstrass318.curve tau).a₆ = (u:ℂ)^6 * (fiber N tau h).a₆ := by
  apply ShortScaling318.exists_scaling_of_j_eq
  rw [fiber_j,ModularWeierstrass318.curve_j]

/-- A selected complex scaling, not a canonical family-wide choice. -/
@[expose] def scaling (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) : ℂˣ :=
  (exists_scaling N tau h).choose

lemma scaling_spec (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    (ModularWeierstrass318.curve tau).a₄ = (scaling N tau h:ℂ)^4 * (fiber N tau h).a₄ ∧
    (ModularWeierstrass318.curve tau).a₆ = (scaling N tau h:ℂ)^6 * (fiber N tau h).a₆ :=
  (exists_scaling N tau h).choose_spec

/-- An actual additive bijection from the evaluated arithmetic model to the
analytic elliptic curve, proved by coordinate scaling and chord-and-tangent addition. -/
@[expose] def pointAddEquiv (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau) :
    (fiber N tau h).toAffine.Point ≃+ (ModularWeierstrass318.curve tau).toAffine.Point :=
  ShortScaling318.pointAddEquiv _ _ (scaling N tau h)
    (scaling_spec N tau h).1 (scaling_spec N tau h).2

@[simp] theorem pointAddEquiv_order (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) (P : (fiber N tau h).toAffine.Point) :
    addOrderOf (pointAddEquiv N tau h P) = addOrderOf P :=
  addOrderOf_injective (pointAddEquiv N tau h).toAddMonoidHom (pointAddEquiv N tau h).injective P

/-- Genuine period labels on the evaluated arithmetic fiber, with both the
ring evaluation and coordinate change constructed rather than supplied as premises. -/
@[expose] def torsionMap (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau)
    (M : ℕ) [NeZero M] : ZMod M × ZMod M →+ (fiber N tau h).toAffine.Point :=
  (pointAddEquiv N tau h).symm.toAddMonoidHom.comp (EllipticTorsion318.torsionMap tau M)

lemma torsionMap_injective (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau)
    (M : ℕ) [NeZero M] : Function.Injective (torsionMap N tau h M) :=
  (pointAddEquiv N tau h).symm.injective.comp (EllipticTorsion318.torsionMap_injective tau M)

lemma torsionMap_order (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau)
    (M : ℕ) [NeZero M] (v : ZMod M × ZMod M) :
    addOrderOf (torsionMap N tau h M v) = M / Nat.gcd M (Nat.gcd v.1.val v.2.val) := by
  rw [addOrderOf_injective (torsionMap N tau h M) (torsionMap_injective N tau h M)]
  exact PrimitiveTorsion318.residue_order M v

lemma torsionMap_surjective_kernel (N : ℕ) [NeZero N] (tau : UpperHalfPlane)
    (h : Admissible tau) (M : ℕ) [NeZero M] (P : (fiber N tau h).toAffine.Point)
    (hP : M • P = 0) : ∃ v, torsionMap N tau h M v = P := by
  have hp : M • pointAddEquiv N tau h P = 0 := by
    rw [←map_nsmul,hP,map_zero]
  obtain ⟨v,hv⟩ := EllipticTorsion318.torsionMap_surjective_kernel tau M _ hp
  refine ⟨v, ?_⟩
  change (pointAddEquiv N tau h).symm (EllipticTorsion318.torsionMap tau M v) = P
  rw [hv,AddEquiv.symm_apply_apply]

/-- Exact-order points of the literal arithmetic fiber, for every positive
order, are precisely the genuine primitive period vectors after the selected scaling. -/
@[expose] def primitiveEquiv (N : ℕ) [NeZero N] (tau : UpperHalfPlane) (h : Admissible tau)
    (M : ℕ) [NeZero M] : {v : ZMod M × ZMod M // PrimitiveTorsion318.Primitive M v} ≃
      {P : (fiber N tau h).toAffine.Point // addOrderOf P = M} :=
  Equiv.ofBijective (fun v => ⟨torsionMap N tau h M v.val, by
    rw [torsionMap_order]
    have hv := v.property
    change Nat.gcd M (Nat.gcd v.val.1.val v.val.2.val)=1 at hv
    simp only [hv,Nat.div_one]⟩)
    ⟨by
      intro v w he
      exact Subtype.ext (torsionMap_injective N tau h M (congrArg Subtype.val he)), by
      intro P
      have hp : M • P.val=0 := by simpa only [P.property] using addOrderOf_nsmul_eq_zero P.val
      obtain ⟨v,hv⟩ := torsionMap_surjective_kernel N tau h M P.val hp
      have ho : addOrderOf (EllipticTorsion318.torsionMap tau M v)=M := by
        rw [PrimitiveTorsion318.point_order]
        have he := torsionMap_order N tau h M v
        rw [hv,P.property] at he
        exact he.symm
      refine ⟨⟨v,(PrimitiveTorsion318.point_order_eq_iff tau M v).mp ho⟩,Subtype.ext hv⟩⟩

end OpenJAnalyticPoints318
