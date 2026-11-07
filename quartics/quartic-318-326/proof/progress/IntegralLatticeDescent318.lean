module
public import HomLatticeDescent318
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public section
namespace IntegralLatticeDescent318
open MatrixCongruence318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
variable {H:Type*} [AddCommGroup H] [Module ℤ H]
variable {n:Type*} [Fintype n] [DecidableEq n]

@[expose] def matrixAction (b:Module.Basis n ℤ H) : (H≃ₗ[ℤ]H)→*Matrix n n ℤ :=
  { toFun:=fun e=>LinearMap.toMatrix b b e.toLinearMap
    map_one':=LinearMap.toMatrix_id b
    map_mul':=fun e f=>LinearMap.toMatrix_mul b e.toLinearMap f.toLinearMap }

/-- The actual lattice congruence on vectors gives the actual matrix
reduction, for any integral basis. -/
theorem matrixAction_mod_three (b:Module.Basis n ℤ H) (e:H≃ₗ[ℤ]H)
    (he:∀x:H,∃y:H,e x-x=(3:ℤ) • y) : modThree (matrixAction b e)=1 := by
  have hd (i j:n):(3:ℤ)∣(matrixAction b e-1) i j := by
    obtain ⟨y,hy⟩:=he (b j)
    refine ⟨b.repr y i,?_⟩
    change (LinearMap.toMatrix b b e.toLinearMap) i j-(1:Matrix n n ℤ) i j=3*b.repr y i
    rw [LinearMap.toMatrix_apply]
    have hbij:b.repr (b j) i=(1:Matrix n n ℤ) i j := by
      simp [Module.Basis.repr_self,Matrix.one_apply,Finsupp.single_apply,eq_comm]
    have hh:=congrArg (fun x:H=>b.repr x i) hy
    have hy3:(3:ℤ) • y=y+y+y := by
      rw [show (3:ℤ)=1+1+1 by decide,add_zsmul,add_zsmul,one_zsmul]
    rw [hy3] at hh
    simp only [map_sub,map_add,Finsupp.sub_apply,Finsupp.add_apply,hbij] at hh
    simpa only [LinearEquiv.coe_coe,LinearEquiv.coe_toLinearMap,show b.repr y i+b.repr y i+b.repr y i=3*b.repr y i by ring] using hh
  apply sub_eq_zero.mp
  rw [←map_one modThree,←map_sub]
  ext i j
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (hd i j)

/-- A finite-image action on an actual integral lattice is trivial when
every action difference is three times another lattice vector. -/
theorem finite_image_action_trivial_of_basis {G:Type*} [Group G]
    (b:Module.Basis n ℤ H) (rho:G→*(H≃ₗ[ℤ]H)) (hfin:(Set.range rho).Finite)
    (hmod:∀g x,∃y:H,rho g x-x=(3:ℤ) • y) : ∀g x,rho g x=x := by
  haveI:Finite rho.range:=hfin
  intro g x
  let z:rho.range:=⟨rho g,⟨g,rfl⟩⟩
  have ho:IsOfFinOrder (rho g):=rho.range.subtype.isOfFinOrder (isOfFinOrder_of_finite z)
  have hm:matrixAction b (rho g)=1 := finite_order_eq_one _
    (matrixAction_mod_three b (rho g) (hmod g)) ((matrixAction b).isOfFinOrder ho)
  have he:(rho g).toLinearMap=LinearMap.id := by
    apply (LinearMap.toMatrix b b).injective
    change matrixAction b (rho g)=LinearMap.toMatrix b b LinearMap.id
    rw [hm]
    exact (LinearMap.toMatrix_id b).symm
  exact congrArg (fun e:H→ₗ[ℤ]H=>e x) he

/-- Basis-free finite-rank free integral-lattice formulation of the Hom
 descent input. No chosen matrix or abstract torsion-free action is assumed. -/
theorem finite_image_action_trivial [Module.Free ℤ H] [Module.Finite ℤ H]
    {G:Type*} [Group G] (rho:G→*(H≃ₗ[ℤ]H)) (hfin:(Set.range rho).Finite)
    (hmod:∀g x,∃y:H,rho g x-x=(3:ℤ) • y) : ∀g x,rho g x=x :=
  finite_image_action_trivial_of_basis (Module.Free.chooseBasis ℤ H) rho hfin hmod

end
end IntegralLatticeDescent318
#print axioms IntegralLatticeDescent318.finite_image_action_trivial
