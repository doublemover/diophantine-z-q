module
public import HolomorphicInverse318
public import ContinuousDescent318
public section
noncomputable section
open UpperHalfPlane GammaOneFiber318 GammaOneAtlas318 PeterssonQuotient318
open DerivativeCocycle318 QuadraticFiber318 ContinuousDescent318
open Filter Topology
namespace FiberQuotientCovering318
set_option maxHeartbeats 0

@[expose] def coordinateHomeomorph : Fiber≃ₜ Prod UpperHalfPlane ℂ where
  toFun:=coordinates
  invFun:=fun p=>⟨p.1,p.2⟩
  left_inv v:=by cases v;rfl
  right_inv p:=by cases p;rfl
  continuous_toFun:=continuous_induced_dom
  continuous_invFun:=by
    apply continuous_induced_rng.mpr
    exact continuous_id

instance : T2Space Fiber := coordinateHomeomorph.isEmbedding.t2Space
instance : LocallyCompactSpace Fiber := coordinateHomeomorph.isOpenEmbedding.locallyCompactSpace

theorem continuous_derivative (g:G) : Continuous (derivative g) := by
  unfold derivative
  apply continuous_const.div
  · unfold denom
    fun_prop
  · intro z
    exact pow_ne_zero 2 (denom_ne_zero g z)

instance continuousConstSMul : ContinuousConstSMul G Fiber where
  continuous_const_smul g := by
    apply continuous_induced_rng.mpr
    change Continuous (fun v:Fiber=>(g • v.point,v.value/(derivative g v.point)^2))
    apply Continuous.prodMk
    · exact (continuous_const_smul g).comp continuous_point
    · exact continuous_value.div (((continuous_derivative g).comp continuous_point).pow 2)
        (fun v=>pow_ne_zero 2 (derivative_ne_zero g v.point))

instance subgroupContinuousConstSMul (N:ℕ) : ContinuousConstSMul (image N) Fiber where
  continuous_const_smul g := continuous_const_smul (g:G)

instance properlyDiscontinuous (N:ℕ) : ProperlyDiscontinuousSMul (image N) Fiber where
  finite_disjoint_inter_image hK hL := by
    have hf:=ProperlyDiscontinuousSMul.finite_disjoint_inter_image
      (Γ:=image N) (hK.image continuous_point) (hL.image continuous_point)
    apply hf.subset
    rintro g ⟨v,⟨u,hu,rfl⟩,hv⟩
    exact ⟨g • u.point,⟨u.point,⟨u,hu,rfl⟩,rfl⟩,⟨g • u,hv,rfl⟩⟩

instance cancelSMul (N:ℕ) [Fact (5≤N)] : IsCancelSMul (image N) Fiber := by
  apply isCancelSMul_iff_eq_one_of_smul_eq.mpr
  intro g v hv
  apply Subtype.ext
  exact image_fixed_eq_one N Fact.out g g.property v.point (congrArg Fiber.point hv)

@[expose] def totalQuotientMap (N:ℕ) : Fiber→Total (image N) :=
  Quotient.mk (MulAction.orbitRel (image N) Fiber)

/-- The actual differential-orbit total-space quotient is itself a genuine covering. -/
theorem total_covering (N:ℕ) (hN:5≤N) :
    IsQuotientCoveringMap (totalQuotientMap N) (image N) := by
  letI:Fact (5≤N):=⟨hN⟩
  exact isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul

theorem total_localHomeomorph (N:ℕ) (hN:5≤N) :
    IsLocalHomeomorph (totalQuotientMap N) := (total_covering N hN).isLocalHomeomorph
end FiberQuotientCovering318
