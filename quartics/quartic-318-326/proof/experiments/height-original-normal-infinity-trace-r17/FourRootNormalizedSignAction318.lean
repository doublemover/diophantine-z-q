module
public import FourRootCompletedHausdorff318
public import FourBinaryCharacters318
public section
noncomputable section
namespace FourRootNormalizedSignAction318
open Set Topology FourRootNormalizedPointCharts318 FourBinaryCharacters318
variable (b:Fin 4→ℂ) (g:FourBinaryCharacters318.Group)
local instance : TopologicalSpace (Completed b):=FourRootGluedTopology318.topology b

lemma sign_ne (i:Fin 4):coordinate (F:=ℂ) i g≠0:=by
  intro h
  have hh:=coordinate_square (F:=ℂ) i g
  rw [h,zero_pow (by decide:2≠0)] at hh
  exact zero_ne_one hh

@[expose] def finite (p:FinitePoints b):FinitePoints b:=
  ⟨(p.val.1,fun i=>coordinate (F:=ℂ) i g*p.val.2 i),by
    intro i
    rw [mul_pow,coordinate_square,one_mul]
    exact p.property i⟩
/-- The normalized infinity ratios transform by epsilon_i/epsilon_0;
all signs square to1, so this is exactly epsilon_i*epsilon_0. -/
@[expose] def infinity (p:InfinityPoints b):InfinityPoints b:=
  ⟨(coordinate (F:=ℂ) 0 g*p.val.1,
    fun i=>coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g*p.val.2 i),by
    change coordinate (F:=ℂ) 0 g*coordinate (F:=ℂ) 0 g*p.val.2 0=1
    rw [p.property.1,mul_one,←pow_two,coordinate_square],by
    intro i
    simp only [mul_pow,coordinate_square,one_mul]
    exact p.property.2 i⟩
@[expose] def signs (s:InfinitySigns):InfinitySigns:=
  ⟨fun i=>coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g*s.val i,by
    change coordinate (F:=ℂ) 0 g*coordinate (F:=ℂ) 0 g*s.val 0=1
    rw [s.property.1,mul_one,←pow_two,coordinate_square],by
    intro i
    simp only [mul_pow,coordinate_square,one_mul]
    exact s.property.2 i⟩
@[expose] def action : Completed b→Completed b
  | .inl p=>.inl (finite b g p)
  | .inr s=>.inr (signs g s)
lemma finite_chart (p:FinitePoints b):action b g (finiteChart b p)=finiteChart b (finite b g p):=rfl
lemma infinity_chart (p:InfinityPoints b):action b g (infinityChart b p)=
    infinityChart b (infinity b g p) := by
  by_cases hp:p.val.1=0
  · have hq:(infinity b g p).val.1=0:=by change coordinate (F:=ℂ) 0 g*p.val.1=0;rw [hp,mul_zero]
    rw [infinityChart,dif_pos hp,infinityChart,dif_pos hq]
    rfl
  · have hq:(infinity b g p).val.1≠0:=mul_ne_zero (sign_ne g 0) hp
    rw [infinityChart_nonzero b p hp,infinityChart_nonzero b _ hq]
    apply congrArg Sum.inl
    apply Subtype.ext
    apply Prod.ext
    · change b 0+(p.val.1^2)⁻¹=b 0+((coordinate (F:=ℂ) 0 g*p.val.1)^2)⁻¹
      rw [mul_pow,coordinate_square,one_mul]
    · funext i
      change coordinate (F:=ℂ) i g*(p.val.2 i/p.val.1)=
        (coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g*p.val.2 i)/
          (coordinate (F:=ℂ) 0 g*p.val.1)
      field_simp [sign_ne g 0,hp]
      <;> ring

lemma finite_continuous : Continuous (finite b g) := by
  have hc:Continuous (fun p:FinitePoints b=>
      fun i=>coordinate (F:=ℂ) i g*p.val.2 i):=
    continuous_pi (fun i=>continuous_const.mul ((continuous_apply i).comp continuous_subtype_val.snd))
  exact (continuous_subtype_val.fst.prodMk hc).subtype_mk _
lemma infinity_continuous : Continuous (infinity b g) := by
  have hu:Continuous (fun p:InfinityPoints b=>coordinate (F:=ℂ) 0 g*p.val.1):=
    continuous_const.mul continuous_subtype_val.fst
  have hs:Continuous (fun p:InfinityPoints b=>
      fun i=>coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g*p.val.2 i):=
    continuous_pi (fun i=>continuous_const.mul ((continuous_apply i).comp continuous_subtype_val.snd))
  exact (hu.prodMk hs).subtype_mk _

/-- Continuity is proved using BOTH independently glued affine charts,
not by transporting an action from the original source. -/
theorem continuous : Continuous (action b g) := by
  apply (FourRootGluedTopology318.continuous_iff b _).mpr
  constructor
  · exact (FourRootGluedTopology318.finiteChart_continuous b).comp (finite_continuous b g)
  · have he:(action b g ∘ infinityChart b)=infinityChart b ∘ infinity b g:=funext (infinity_chart b g)
    rw [he]
    exact (FourRootGluedTopology318.infinityChart_continuous b).comp (infinity_continuous b g)

lemma involutive : Function.Involutive (action b g) := by
  intro p
  rcases p with p|s
  · apply congrArg Sum.inl
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · funext i
      change coordinate (F:=ℂ) i g*(coordinate (F:=ℂ) i g*p.val.2 i)=p.val.2 i
      rw [←mul_assoc,←pow_two,coordinate_square,one_mul]
  · apply congrArg Sum.inr
    apply Subtype.ext
    funext i
    change (coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g)*
      ((coordinate (F:=ℂ) i g*coordinate (F:=ℂ) 0 g)*s.val i)=s.val i
    rw [←mul_assoc,←pow_two,mul_pow,coordinate_square,coordinate_square,one_mul,one_mul]

@[expose] def homeomorph : Completed b≃ₜCompleted b where
  toEquiv:=⟨action b g,action b g,involutive b g,involutive b g⟩
  continuous_toFun:=continuous b g
  continuous_invFun:=continuous b g
end FourRootNormalizedSignAction318
