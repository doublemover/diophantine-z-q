module
public import ModuleLocalGluing318
public section
noncomputable section
namespace ModuleLocalIsomorphism318
open AlgebraicGeometry CategoryTheory Opposite
open ModuleLocalGluing318
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {X : Scheme.{u}} {M N : X.Modules} {ι : Type u} {U : ι → X.Opens}
    (D : LocalData M N U) (hc : ⊤ ≤ iSup U)
    (hb : ∀ i V (hV : V≤U i), Function.Bijective (D.map i V hV))

@[expose] def localEquiv (i : ι) (V : X.Opens) (hV : V≤U i) :
    Γ(M,V) ≃ₗ[Γ(X,V)] Γ(N,V) := LinearEquiv.ofBijective (D.map i V hV) (hb i V hV)

/-- The inverse local maps obey the same whole-subopen compatibility and naturality. -/
@[expose] def inverseData : LocalData N M U where
  map i V hV := (localEquiv D hb i V hV).symm.toLinearMap
  natural i V W hV hW s := by
    apply (localEquiv D hb i W (hW.trans hV)).injective
    change D.map i W (hW.trans hV) (res M hW ((localEquiv D hb i V hV).symm s))=
      (localEquiv D hb i W (hW.trans hV)) ((localEquiv D hb i W (hW.trans hV)).symm (res N hW s))
    rw [LinearEquiv.apply_symm_apply,←D.natural]
    change res N hW ((localEquiv D hb i V hV) ((localEquiv D hb i V hV).symm s))=_
    rw [LinearEquiv.apply_symm_apply]
  compatible i j V hi hj s := by
    apply (localEquiv D hb i V hi).injective
    change (localEquiv D hb i V hi) ((localEquiv D hb i V hi).symm s)=
      D.map i V hi ((localEquiv D hb j V hj).symm s)
    rw [LinearEquiv.apply_symm_apply,D.compatible i j V hi hj]
    exact (localEquiv D hb j V hj).apply_symm_apply s |>.symm

/-- The actual global isomorphism obtained by gluing compatible full-chart
linear isomorphisms. Its inverse is separately glued and both identities are checked. -/
@[expose] def iso : M ≅ N where
  hom := ModuleLocalGluing318.hom D hc
  inv := ModuleLocalGluing318.hom (inverseData D hb) hc
  hom_inv_id := by
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    change value (inverseData D hb) hc W (value D hc W s)=s
    apply ext_value hc W
    intro i
    rw [value_restrict]
    change (localEquiv D hb i _ inf_le_right).symm
      (res N inf_le_left (value D hc W s))=res M inf_le_left s
    rw [value_restrict]
    exact (localEquiv D hb i _ inf_le_right).symm_apply_apply (res M inf_le_left s)
  inv_hom_id := by
    apply Scheme.Modules.hom_ext
    intro W
    ext s
    change value D hc W (value (inverseData D hb) hc W s)=s
    apply ext_value hc W
    intro i
    rw [value_restrict]
    change (localEquiv D hb i _ inf_le_right)
      (res M inf_le_left (value (inverseData D hb) hc W s))=res N inf_le_left s
    rw [value_restrict]
    exact (localEquiv D hb i _ inf_le_right).apply_symm_apply (res N inf_le_left s)
end ModuleLocalIsomorphism318
