module
public import IntrinsicTensorSheaf318
public section
noncomputable section
namespace TensorScalarIso318
open CategoryTheory TensorProduct
open scoped TensorProduct
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) (M N : ModuleCat S)

local instance inversePair : RingHomInvPair e.toRingHom e.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv e
local instance inversePairSymm : RingHomInvPair e.symm.toRingHom e.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm e

/-- New continuation, not part of the pre-reset checked sources. -/
@[expose] def scalarIdentity :
    LinearEquiv e.symm.toRingHom (σ':=e.toRingHom) M
      ((ModuleCat.restrictScalars e.toRingHom).obj M) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' s m := by
    change s • m = e (e.symm s) • m
    rw [e.apply_symm_apply]

@[expose] def tensorEquiv :
    (ModuleCat.restrictScalars e.toRingHom).obj (ModuleCat.of S (M ⊗[S] N)) ≃ₗ[R]
      ((ModuleCat.restrictScalars e.toRingHom).obj M) ⊗[R]
        ((ModuleCat.restrictScalars e.toRingHom).obj N) := by
  let q := TensorProduct.congr (scalarIdentity e M) (scalarIdentity e N)
  refine { q.toAddEquiv with map_smul' := ?_ }
  intro r z
  change q (e r • z) = r • q z
  rw [q.map_smulₛₗ]
  change e.symm (e r) • q (show M ⊗[S] N from z) = r • q (show M ⊗[S] N from z)
  rw [e.symm_apply_apply]

theorem tensorEquiv_tmul (m : M) (n : N) :
    tensorEquiv e M N (m ⊗ₜ[S] n) =
      (show (ModuleCat.restrictScalars e.toRingHom).obj M from m) ⊗ₜ[R]
        (show (ModuleCat.restrictScalars e.toRingHom).obj N from n) := rfl
end TensorScalarIso318
