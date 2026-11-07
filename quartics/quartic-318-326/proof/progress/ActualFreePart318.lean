module
public import ActualMordellWeil318
public import GlobalTorsionOddIndex318
public import Mathlib.Algebra.Module.PID
public import Mathlib.GroupTheory.IndexNSmul
public section
namespace ActualFreePart318
open ConcreteG8Domain LocalGenerator318 GlobalGeneratorPoints318 ActualDoubleQuotient318
open WeierstrassCurve.Affine
set_option maxHeartbeats 0
noncomputable section

instance : AddGroup.FG E.Point := ActualMordellWeil318.finitely_generated
@[expose] abbrev FreePart := E.Point ⧸ Submodule.torsion ℤ E.Point
@[expose] def quotientMap : E.Point →ₗ[ℤ] FreePart := (Submodule.torsion ℤ E.Point).mkQ

theorem quotientMap_zero_iff (Q:E.Point) : quotientMap Q=0 ↔ IsOfFinAddOrder Q := by
  rw [show quotientMap Q=Submodule.Quotient.mk Q by rfl,Submodule.Quotient.mk_eq_zero]
  change Q∈(Submodule.torsion ℤ E.Point).toAddSubgroup ↔ _
  rw [Submodule.torsion_int,AddCommGroup.mem_torsion]

theorem quotientMap_two_torsion (Q:E.Point) (hQ:Q+Q=0) : quotientMap Q=0 := by
  apply (quotientMap_zero_iff Q).mpr
  exact isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨2,by decide,by simpa only [two_nsmul] using hQ⟩

@[expose] def torsionPoint (i:Fin 4) : E.Point := ![0,T 0,T 1,T 2] i

theorem torsionPoint_double (i:Fin 4) : torsionPoint i+torsionPoint i=0 := by
  fin_cases i <;> simp only [torsionPoint,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  · simp
  all_goals exact double_T _

theorem torsionPoint_injective : Function.Injective torsionPoint := by
  intro i j h
  fin_cases i <;> fin_cases j <;>
    simp_all [torsionPoint,T,Point.some.injEq,torsionX,pair,QuadraticAlgebra.ext_iff] <;> norm_num at h

@[expose] abbrev basis := Module.finBasis ℤ FreePart

/-- The chosen finite quotient bound constrains the actual free part,
provided the independently proved torsion statement is supplied. -/
theorem free_rank_le_one
    (ht:∀Q:E.Point,IsOfFinAddOrder Q → Q+Q=0) : Module.finrank ℤ FreePart≤1 := by
  by_contra! hn
  let i₀:Fin (Module.finrank ℤ FreePart):=⟨0,by omega⟩
  let i₁:Fin (Module.finrank ℤ FreePart):=⟨1,by omega⟩
  have hi:i₀≠i₁ := by intro h; have hh:=congrArg Fin.val h; simp [i₀,i₁] at hh
  obtain ⟨G₀,hG₀⟩:∃G:E.Point,quotientMap G=basis i₀ := (Submodule.torsion ℤ E.Point).mkQ_surjective _
  obtain ⟨G₁,hG₁⟩:∃G:E.Point,quotientMap G=basis i₁ := (Submodule.torsion ℤ E.Point).mkQ_surjective _
  let point : Fin 2×Fin 2×Fin 4 → E.Point := fun a=>
    (a.1.val:ℤ) • G₀+(a.2.1.val:ℤ) • G₁+torsionPoint a.2.2
  let code : Fin 2×Fin 2×Fin 4 → Fin 10 := fun a=>pointCode (point a)
  have hc:Function.Injective code := by
    intro a b hab
    obtain ⟨U,hU⟩:=same_code_difference_double (point a) (point b) hab
    have hq:=congrArg quotientMap hU
    simp only [map_add,map_sub,point,map_zsmul,hG₀,hG₁,
      quotientMap_two_torsion _ (torsionPoint_double _),add_zero] at hq
    have h₀:=congrArg (fun z:FreePart=>(basis.repr z) i₀) hq
    have h₁:=congrArg (fun z:FreePart=>(basis.repr z) i₁) hq
    simp only [map_add,map_sub,map_zsmul,basis.repr_self,Finsupp.add_apply,Finsupp.sub_apply,
      Finsupp.smul_apply,Finsupp.single_apply,if_pos rfl,if_neg hi,if_neg hi.symm,smul_eq_mul,
      mul_one,mul_zero,add_zero,zero_add] at h₀ h₁
    simp only [ite_true,mul_one] at h₀ h₁
    have ha:a.1=b.1 := by apply Fin.ext; have ha:=a.1.isLt; have hb:=b.1.isLt; omega
    have hb:a.2.1=b.2.1 := by apply Fin.ext; have ha:=a.2.1.isLt; have hb:=b.2.1.isLt; omega
    have hz:quotientMap U=0 := by
      rw [ha,hb] at hq
      have htwo:(2:ℤ) • quotientMap U=0 := by simpa only [two_zsmul,sub_self] using hq
      exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)
    have hUt:=ht U ((quotientMap_zero_iff U).mp hz)
    have hT:torsionPoint a.2.2=torsionPoint b.2.2 := by
      rw [hUt] at hU
      dsimp only [point] at hU
      rw [ha,hb] at hU
      apply sub_eq_zero.mp
      have hh:(b.1.val:ℤ) • G₀+(b.2.1.val:ℤ) • G₁+torsionPoint a.2.2-
        ((b.1.val:ℤ) • G₀+(b.2.1.val:ℤ) • G₁+torsionPoint b.2.2)=
        torsionPoint a.2.2-torsionPoint b.2.2 := by abel
      rw [hh] at hU
      exact hU.symm
    have hc:=torsionPoint_injective hT
    exact Prod.ext ha (Prod.ext hb hc)
  have hcard:=Nat.card_le_card_of_injective code hc
  norm_num [Nat.card_prod,Nat.card_fin] at hcard

end
end ActualFreePart318
#print axioms ActualFreePart318.free_rank_le_one
