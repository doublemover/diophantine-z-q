module
public import NormalizedLegendreFieldPoints318
public import AnalyticImplicitGraph318
public section
noncomputable section
namespace LegendreIndependentGraphs318
open NormalizedLegendreProjectiveModel318
open Filter
open scoped Topology
set_option maxHeartbeats 2400000
variable (l : ℂ) [Fact (l≠0 ∧ l≠1)]

/-- Independent equations of the actual scheme's two affine charts. -/
@[expose] def finiteEquation (p : ℂ × ℂ) : ℂ := p.2^2-p.1^3-A l*p.1-B l
@[expose] def infinityEquation (p : ℂ × ℂ) : ℂ := p.2-p.1^3-A l*p.1*p.2^2-B l*p.2^3
lemma finite_analytic (p : ℂ × ℂ) : AnalyticAt ℂ (finiteEquation l) p := by
  unfold finiteEquation
  fun_prop
lemma infinity_analytic (p : ℂ × ℂ) : AnalyticAt ℂ (infinityEquation l) p := by
  unfold infinityEquation
  fun_prop

/-- Smoothness of the literal finite plane equation is established from
its actual discriminant, independently of the period parametrization. -/
lemma finite_partial_nonzero (p : ℂ × ℂ) (hp : finiteEquation l p=0) :
    2*p.2≠0 ∨ -(3*p.1^2+A l)≠0 := by
  by_contra h
  push Not at h
  have hy : p.2=0 := by linear_combination h.1/2
  have ha : A l= -3*p.1^2 := by linear_combination -h.2
  have hb : B l=2*p.1^3 := by
    dsimp [finiteEquation] at hp
    rw [hy,ha] at hp
    linear_combination -hp
  have hl := (Fact.out : l≠0 ∧ l≠1)
  have hd := discriminant_ne l hl.1 hl.2
  apply hd
  rw [ha,hb]
  ring

lemma finite_y_derivative (p : ℂ × ℂ) :
    HasDerivAt (fun y : ℂ => finiteEquation l (p.1,y)) (2*p.2) p.2 := by
  convert ((((hasDerivAt_id p.2).pow 2).sub_const (p.1^3)).sub_const (A l*p.1)).sub_const (B l) using 1 <;>
    simp [finiteEquation] <;> ring
lemma finite_x_derivative (p : ℂ × ℂ) :
    HasDerivAt (fun x : ℂ => finiteEquation l (x,p.2)) (-(3*p.1^2+A l)) p.1 := by
  convert (((hasDerivAt_const p.1 (p.2^2)).sub ((hasDerivAt_id p.1).pow 3)).sub
    ((hasDerivAt_id p.1).const_mul (A l))).sub_const (B l) using 1 <;>
    simp [finiteEquation] <;> ring

/-- Every actual finite plane point has an independent holomorphic graph
with uniqueness on a FULL ambient neighborhood. Either coordinate may
be selected; no finite point or vertical tangent is discarded. -/
theorem finite_graph (p : ℂ × ℂ) (hp : finiteEquation l p=0) :
    (∃ g : ℂ → ℂ,AnalyticAt ℂ g p.1 ∧ g p.1=p.2 ∧
      (∀ᶠ z in 𝓝 p.1,finiteEquation l (z,g z)=0) ∧
      (∀ᶠ v in 𝓝 p,finiteEquation l v=0 ↔ g v.1=v.2)) ∨
    (∃ g : ℂ → ℂ,AnalyticAt ℂ g p.2 ∧ g p.2=p.1 ∧
      (∀ᶠ z in 𝓝 p.2,finiteEquation l (g z,z)=0) ∧
      (∀ᶠ v in 𝓝 p,finiteEquation l v=0 ↔ g v.2=v.1)) := by
  rcases finite_partial_nonzero l p hp with hy | hx
  · left
    simpa only [hp] using AnalyticImplicitGraph318.exists_graph
      (finite_analytic l p) (finite_y_derivative l p) hy
  · right
    have hf : AnalyticAt ℂ (fun v : ℂ × ℂ => finiteEquation l (v.2,v.1)) (p.2,p.1) := by
      unfold finiteEquation
      fun_prop
    obtain ⟨g,hg,hval,he,hu⟩ := AnalyticImplicitGraph318.exists_graph
      hf (finite_x_derivative l p) hx
    refine ⟨g,hg,hval,by simpa only [hp] using he,?_⟩
    have ht : Tendsto (fun v : ℂ × ℂ => (v.2,v.1)) (𝓝 p) (𝓝 (p.2,p.1)) := by
      exact (by fun_prop : ContinuousAt (fun v : ℂ × ℂ => (v.2,v.1)) p).tendsto
    simpa only [hp] using ht.eventually hu

/-- The actual infinity equation has unit vertical derivative at its
origin, giving an independent analytic infinity graph with uniqueness. -/
theorem infinity_graph : ∃ g : ℂ → ℂ,AnalyticAt ℂ g 0 ∧ g 0=0 ∧
    (∀ᶠ z in 𝓝 (0:ℂ),infinityEquation l (z,g z)=0) ∧
    (∀ᶠ v in 𝓝 ((0,0):ℂ × ℂ),infinityEquation l v=0 ↔ g v.1=v.2) := by
  have hd : HasDerivAt (fun y : ℂ => infinityEquation l (0,y)) 1 0 := by
    convert (hasDerivAt_id (0:ℂ)).sub (((hasDerivAt_id (0:ℂ)).pow 3).const_mul (B l)) using 1 <;>
      simp [infinityEquation]
  simpa only [infinityEquation,zero_pow (by decide : 3≠0),zero_pow (by decide : 2≠0),
    mul_zero,zero_mul,sub_zero] using
    AnalyticImplicitGraph318.exists_graph (infinity_analytic l (0,0)) hd one_ne_zero
end LegendreIndependentGraphs318
