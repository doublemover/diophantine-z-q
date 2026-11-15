module
public import OvalInvariantClock318
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public section
noncomputable section

/-! The invariant clock gives an actual additive real flow on the whole
quartic oval. Addition is proved by polynomial ODE uniqueness. -/
namespace OvalFlowAddition318
open RealQuarticGroup318 ReciprocalGroup318 OvalInvariantClock318
open Set
local instance : AddCommGroup (Oval 1) := group 1 (by norm_num)
set_option maxHeartbeats 3000000

@[expose] def vectorField (p : ℝ × ℝ) : ℝ × ℝ := (p.2,-2*p.1^3)

lemma oval_bounded (p : Oval 1) : p.val∈Metric.closedBall (0:ℝ × ℝ) 2 := by
  obtain ⟨t,hu,hv⟩ := RealQuarticOvalCover318.oval_surjective (d:=1) (by norm_num)
    p.val.1 p.val.2 p.property
  have hub : |p.val.1|≤1 := by
    have he : Real.sin t=p.val.1 := by
      simpa [RealQuarticOvalCover318.u,RealQuarticOvalCover318.radius] using hu
    rw [←he]
    exact Real.abs_sin_le_one t
  have hvb : |p.val.2|≤1 := by
    apply (sq_le_one_iff_abs_le_one _).mp
    have he := p.property
    simp only [one_mul] at he
    nlinarith [sq_nonneg (p.val.1^2)]
  rw [Metric.mem_closedBall,dist_zero_right,Prod.norm_def,max_le_iff]
  simp only [Real.norm_eq_abs]
  exact ⟨le_trans hub (by norm_num),le_trans hvb (by norm_num)⟩

/-- Uniqueness is applied on a genuine compact convex neighborhood containing
all oval trajectories. The polynomial vector field is proved C^1 there. -/
lemma trajectory_unique (f g : ℝ → Oval 1)
    (hf : ∀ t, HasDerivAt (fun s => (f s).val) (vectorField (f t).val) t)
    (hg : ∀ t, HasDerivAt (fun s => (g s).val) (vectorField (g t).val) t)
    (hzero : f 0=g 0) : f=g := by
  have hF : ContDiff ℝ 1 vectorField := by unfold vectorField; fun_prop
  obtain ⟨K,hK⟩ := hF.contDiffOn.exists_lipschitzOnWith (by norm_num)
    (convex_closedBall (0:ℝ × ℝ) 2) (isCompact_closedBall (0:ℝ × ℝ) 2)
  have he : (fun t => (f t).val)=(fun t => (g t).val) :=
    ODE_solution_unique_univ (v:=fun _ => vectorField)
      (s:=fun _ => Metric.closedBall (0:ℝ × ℝ) 2) (t₀:=0)
      (fun _ => hK) (fun t => ⟨hf t,oval_bounded (f t)⟩)
      (fun t => ⟨hg t,oval_bounded (g t)⟩) (congrArg Subtype.val hzero)
  funext t
  exact Subtype.ext (congrFun he t)

private lemma denominator_ne (u a : ℝ) : 1+u^2*a^2≠0 := by positivity

private lemma tangentU (u v a b : ℝ) (hc : v^2=1-u^4) :
    ((v*b+a*(-2*u^3))*(1+u^2*a^2)-(u*b+a*v)*(2*u*v*a^2))/(1+u^2*a^2)^2=
      sumV 1 u v a b := by
  unfold sumV
  simp only [one_mul]
  field_simp [denominator_ne u a]
  linear_combination -2*u*a^3*hc

private lemma tangentV (u v a b : ℝ) (hc : v^2=1-u^4) (hb : b^2=1-a^4) :
    ((-2*a^3*v+2*a^2*b*u^5-2*a^2*b*u*v^2-6*a*u^2*v-2*b*u^3)*(1+u^2*a^2)^2-
      (v*b*(1-u^2*a^2)-2*u*a*(u^2+a^2))*(2*(1+u^2*a^2)*(2*u*v*a^2)))/
        ((1+u^2*a^2)^2)^2= -2*(sumU 1 u v a b)^3 := by
  have hpoly :
      (-2*a^3*v+2*a^2*b*u^5-2*a^2*b*u*v^2-6*a*u^2*v-2*b*u^3)*(1+u^2*a^2)^2-
        (v*b*(1-u^2*a^2)-2*u*a*(u^2+a^2))*(2*(1+u^2*a^2)*(2*u*v*a^2))=
        -2*(u*b+a*v)^3*(1+u^2*a^2) := by
    linear_combination
      (1+u^2*a^2)*(2*a^3*(a*b*u^3+v))*hc+
      (1+u^2*a^2)*(2*u^2*(3*a*v+b*u))*hb
  rw [hpoly]
  unfold sumU
  simp only [one_mul]
  field_simp [denominator_ne u a]
  <;> ring

set_option backward.isDefEq.respectTransparency false in
/-- Every fixed group translation preserves the actual invariant vector
field, including tangent, inverse and zero-ordinate points. -/
lemma translated_hasDeriv (f : ℝ → Oval 1) (q : Oval 1) (t : ℝ)
    (hf : HasDerivAt (fun s => (f s).val) (vectorField (f t).val) t) :
    HasDerivAt (fun s => (f s+q).val) (vectorField (f t+q).val) t := by
  let u : ℝ → ℝ := fun s => (f s).val.1
  let v : ℝ → ℝ := fun s => (f s).val.2
  let a := q.val.1
  let b := q.val.2
  have hu : HasDerivAt u (v t) t := hf.fst
  have hv : HasDerivAt v (-2*(u t)^3) t := hf.snd
  have hc : (v t)^2=1-(u t)^4 := by simpa only [one_mul] using (f t).property
  have hb : b^2=1-a^4 := by simpa only [one_mul] using q.property
  have hd : HasDerivAt (fun s => 1+(u s)^2*a^2) (2*u t*v t*a^2) t := by
    convert ((hu.pow 2).mul_const (a^2)).const_add 1 using 1 <;> ring
  have hnumU : HasDerivAt (fun s => u s*b+a*v s) (v t*b+a*(-2*(u t)^3)) t :=
    (hu.mul_const b).add (hv.const_mul a)
  have hU := hnumU.div hd (denominator_ne (u t) a)
  rw [tangentU (u t) (v t) a b hc] at hU
  have hnumV : HasDerivAt
      (fun s => v s*b*(1-(u s)^2*a^2)-2*u s*a*((u s)^2+a^2))
      (-2*a^3*v t+2*a^2*b*(u t)^5-2*a^2*b*u t*(v t)^2-
        6*a*(u t)^2*v t-2*b*(u t)^3) t := by
    convert (((hv.mul_const b).mul (((hu.pow 2).mul_const (a^2)).const_sub 1)).sub
      (((hu.const_mul 2).mul_const a).mul ((hu.pow 2).add_const (a^2)))) using 1 <;> simp only [Pi.pow_apply] <;> ring
  have hd2 : HasDerivAt (fun s => (1+(u s)^2*a^2)^2)
      (2*(1+(u t)^2*a^2)*(2*u t*v t*a^2)) t := by
    convert hd.pow 2 using 1 <;> ring
  have hV := hnumV.div hd2 (pow_ne_zero 2 (denominator_ne (u t) a))
  rw [tangentV (u t) (v t) a b hc hb] at hV
  change HasDerivAt (fun s => (sumU 1 (u s) (v s) a b,sumV 1 (u s) (v s) a b))
    (sumV 1 (u t) (v t) a b,-2*(sumU 1 (u t) (v t) a b)^3) t
  have hfunU : ((fun s => u s*b+a*v s)/(fun s => 1+(u s)^2*a^2))=
      (fun s => sumU 1 (u s) (v s) a b) := by
    funext s
    simp only [Pi.div_apply,sumU,one_mul,mul_one]
  have hfunV : ((fun s => v s*b*(1-(u s)^2*a^2)-2*u s*a*((u s)^2+a^2))/
      (fun s => (1+(u s)^2*a^2)^2))=(fun s => sumV 1 (u s) (v s) a b) := by
    funext s
    simp only [Pi.div_apply,sumV,one_mul,mul_one]
  rw [hfunU] at hU
  rw [hfunV] at hV
  exact HasDerivAt.prodMk hU hV

set_option backward.isDefEq.respectTransparency false in
/-- The real invariant-clock flow respects the existing quartic group law.
No new group law is transported onto the oval to make this true. -/
theorem flow_add (s t : ℝ) : flow (s+t)=flow s+flow t := by
  have hf (x : ℝ) : HasDerivAt (fun y => (flow (y+t)).val)
      (vectorField (flow (x+t)).val) x := by
    have hi : HasDerivAt (fun y : ℝ => y+t) 1 x := (hasDerivAt_id x).add_const t
    have ho : HasDerivAt (fun y => (flow y).val)
        (vectorField (flow (x+t)).val) ((fun y : ℝ => y+t) x) := flow_hasDeriv (x+t)
    have hh := ho.scomp x hi
    change HasDerivAt (fun y => (flow (y+t)).val)
      (1 • vectorField (flow (x+t)).val) x at hh
    simpa only [one_smul] using hh
  have hg (x : ℝ) : HasDerivAt (fun y => (flow y+flow t).val)
      (vectorField (flow x+flow t).val) x :=
    translated_hasDeriv flow (flow t) x (flow_hasDeriv x)
  have hz : flow 0=(0:Oval 1) := Subtype.ext flow_zero
  have he := trajectory_unique (fun x => flow (x+t)) (fun x => flow x+flow t) hf hg
    (by simp only [_root_.zero_add,hz])
  exact congrFun he s

@[expose] def flowHom : ℝ →+ Oval 1 where
  toFun := flow
  map_zero' := Subtype.ext flow_zero
  map_add' := flow_add

end OvalFlowAddition318
