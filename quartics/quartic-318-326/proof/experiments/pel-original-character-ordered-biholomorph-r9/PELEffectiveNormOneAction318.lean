module
public import PELNormOneBaseAction318
public section
noncomputable section
namespace PELEffectiveNormOneAction318
open QuaternionicJointPeriodTopology318 PELJointNormOneAction318 PELNormOneBaseAction318
open PELPrincipalBaseHolomorphy318
open scoped Manifold ContDiff
set_option maxHeartbeats 1500000

/-- The effective group is the IMAGE of the original norm-one units acting
on the original upper half-plane, not a postulated projective arithmetic group. -/
@[expose] def permutation : normOneUnits →* Equiv.Perm HalfPlane where
  toFun u :=
    { toFun := fun τ => u • τ
      invFun := fun τ => u⁻¹ • τ
      left_inv τ := by rw [smul_smul,inv_mul_cancel,one_smul]
      right_inv τ := by rw [smul_smul,mul_inv_cancel,one_smul] }
  map_one' := by ext τ; exact one_smul _ _
  map_mul' u v := by ext τ; exact mul_smul u v τ

@[expose] def effectiveGroup : Subgroup (Equiv.Perm HalfPlane) := permutation.range
@[expose] def effectiveMap : normOneUnits →* effectiveGroup := permutation.rangeRestrict

theorem effectiveMap_surjective : Function.Surjective effectiveMap := by
  rintro ⟨g,u,hu⟩
  exact ⟨u,Subtype.ext hu⟩

instance : MulAction effectiveGroup HalfPlane where
  smul g τ := g.val τ
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem effectiveMap_action (u : normOneUnits) (τ : HalfPlane) : effectiveMap u • τ=u • τ := rfl

theorem effectiveMap_eq_one_iff (u : normOneUnits) :
    effectiveMap u=1 ↔ u.val=1 ∨ u.val= -1 := by
  constructor
  · intro h
    apply stabilizer_sign u basePoint
    change effectiveMap u • basePoint=basePoint
    rw [h,one_smul]
  · intro h
    apply Subtype.ext
    apply Equiv.ext
    intro τ
    apply Subtype.ext
    exact sign_parameter u.val h τ

/-- After removing precisely the actual scalar-sign kernel, all stabilizers
are trivial, using the original mod5/mod7 integral-order obstruction. -/
instance effective_free : IsCancelSMul effectiveGroup HalfPlane :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (by
    intro g τ h
    obtain ⟨u,rfl⟩ := effectiveMap_surjective g
    exact (effectiveMap_eq_one_iff u).mpr (stabilizer_sign u τ h))

instance effective_proper : ProperlyDiscontinuousSMul effectiveGroup HalfPlane where
  finite_disjoint_inter_image := by
    intro K L hK hL
    have hf := finite_disjoint_inter_image (Γ:=normOneUnits) hK hL
    apply (hf.image effectiveMap).subset
    intro g hg
    obtain ⟨u,rfl⟩ := effectiveMap_surjective g
    exact ⟨u,hg,rfl⟩

local instance : ChartedSpace ℂ HalfPlane := halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω HalfPlane := halfPlane_manifold

theorem effective_holomorphic (g : effectiveGroup) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fun τ : HalfPlane => g • τ) := by
  obtain ⟨u,rfl⟩ := effectiveMap_surjective g
  exact base_holomorphic u

instance effective_continuous : ContinuousConstSMul effectiveGroup HalfPlane where
  continuous_const_smul g := (effective_holomorphic g).continuous
end PELEffectiveNormOneAction318
