module
public import ThreeTorsionDiamond318
public section
noncomputable section
namespace ThreeTorsionTorsor318
open ThreeTorsionAlgebra318 ThreeTorsionSplitData318
open PrimitiveDiamond318 InvariantBaseChange318
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable {R:Type*} [CommRing R] [Nontrivial R] (A B:R) [Invertible (3:R)]
  (hD:IsUnit (-16*(4*A^3+27*B^2))) (H:Subgroup (ZMod 3)ˣ)

@[expose] def action : H→Ring A B hD≃ₐ[R]Ring A B hD :=
  fun g=>ThreeTorsionDiamond318.diamond A B hD g.val

/-- The actual canonical action tensor map is an isomorphism. Neither the
cover algebra, the splitting extension, nor scalar freeness is a premise. -/
@[expose] def torsorEquiv :
    Ring A B hD⊗[invariants (action A B hD H)]Ring A B hD≃ₐ[invariants (action A B hD H)]
      (H→Ring A B hD) :=
  primitiveTorsorEquiv 3 (T A B hD) H (action A B hD H)
    (ThreeTorsionDiamond318.primitiveSplit A B hD)
    (fun g b p=>ThreeTorsionDiamond318.equivariant A B hD g.val b p)

theorem torsorEquiv_tmul (b c:Ring A B hD) (g:H) :
    torsorEquiv A B hD H (b⊗ₜ[invariants (action A B hD H)]c) g=
      b*ThreeTorsionDiamond318.diamond A B hD g.val c := rfl

end ThreeTorsionTorsor318
