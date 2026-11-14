module
public import OriginalPeriodCompletedSchemeBijection318
public import AnalyticImplicitGraph318
public section
noncomputable section
namespace OriginalPeriodIndependentGraphs318
open OriginalPeriodProjectiveModel318
open ComplexAffineFreeTranslation318 Filter
open scoped Topology
set_option maxHeartbeats 2400000
variable (L : AddSubgroup ℂ) [DiscreteTopology L] [CompactSpace (Torus L)]

/-- Independent equations of the actual scheme's two affine charts. -/
@[expose] def finiteEquation (p : ℂ × ℂ) : ℂ := p.2^2-p.1^3-A L*p.1-B L
@[expose] def infinityEquation (p : ℂ × ℂ) : ℂ := p.2-p.1^3-A L*p.1*p.2^2-B L*p.2^3
lemma finite_analytic (p : ℂ × ℂ) : AnalyticAt ℂ (finiteEquation L) p := by
  unfold finiteEquation
  fun_prop
lemma infinity_analytic (p : ℂ × ℂ) : AnalyticAt ℂ (infinityEquation L) p := by
  unfold infinityEquation
  fun_prop

/-- Smoothness of the literal finite plane equation is established from
its actual discriminant, independently of the period parametrization. -/
lemma finite_partial_nonzero (p : ℂ × ℂ) (hp : finiteEquation L p=0) :
    2*p.2≠0 ∨ -(3*p.1^2+A L)≠0 := by
  by_contra h
  push Not at h
  have hy : p.2=0 := by linear_combination h.1/2
  have ha : A L= -3*p.1^2 := by linear_combination -h.2
  have hb : B L=2*p.1^3 := by
    dsimp [finiteEquation] at hp
    rw [hy,ha] at hp
    linear_combination -hp
  have hd := (isUnit_iff_ne_zero.mp (discriminant_unit L))
  apply hd
  rw [ha,hb]
  ring

lemma finite_y_derivative (p : ℂ × ℂ) :
    HasDerivAt (fun y : ℂ => finiteEquation L (p.1,y)) (2*p.2) p.2 := by
  convert ((((hasDerivAt_id p.2).pow 2).sub_const (p.1^3)).sub_const (A L*p.1)).sub_const (B L) using 1 <;>
    simp [finiteEquation] <;> ring
lemma finite_x_derivative (p : ℂ × ℂ) :
    HasDerivAt (fun x : ℂ => finiteEquation L (x,p.2)) (-(3*p.1^2+A L)) p.1 := by
  convert (((hasDerivAt_const p.1 (p.2^2)).sub ((hasDerivAt_id p.1).pow 3)).sub
    ((hasDerivAt_id p.1).const_mul (A L))).sub_const (B L) using 1 <;>
    simp [finiteEquation] <;> ring

/-- Every actual finite plane point has an independent holomorphic graph
with uniqueness on a FULL ambient neighborhood. Either coordinate may
be selected; no finite point or vertical tangent is discarded. -/
theorem finite_graph (p : ℂ × ℂ) (hp : finiteEquation L p=0) :
    (∃ g : ℂ → ℂ,AnalyticAt ℂ g p.1 ∧ g p.1=p.2 ∧
      (∀ᶠ z in 𝓝 p.1,finiteEquation L (z,g z)=0) ∧
      (∀ᶠ v in 𝓝 p,finiteEquation L v=0 ↔ g v.1=v.2)) ∨
    (∃ g : ℂ → ℂ,AnalyticAt ℂ g p.2 ∧ g p.2=p.1 ∧
      (∀ᶠ z in 𝓝 p.2,finiteEquation L (g z,z)=0) ∧
      (∀ᶠ v in 𝓝 p,finiteEquation L v=0 ↔ g v.2=v.1)) := by
  rcases finite_partial_nonzero L p hp with hy | hx
  · left
    simpa only [hp] using AnalyticImplicitGraph318.exists_graph
      (finite_analytic L p) (finite_y_derivative L p) hy
  · right
    have hf : AnalyticAt ℂ (fun v : ℂ × ℂ => finiteEquation L (v.2,v.1)) (p.2,p.1) := by
      unfold finiteEquation
      fun_prop
    obtain ⟨g,hg,hval,he,hu⟩ := AnalyticImplicitGraph318.exists_graph
      hf (finite_x_derivative L p) hx
    refine ⟨g,hg,hval,by simpa only [hp] using he,?_⟩
    have ht : Tendsto (fun v : ℂ × ℂ => (v.2,v.1)) (𝓝 p) (𝓝 (p.2,p.1)) := by
      exact (by fun_prop : ContinuousAt (fun v : ℂ × ℂ => (v.2,v.1)) p).tendsto
    simpa only [hp] using ht.eventually hu

/-- The actual infinity equation has unit vertical derivative at its
origin, giving an independent analytic infinity graph with uniqueness. -/
theorem infinity_graph : ∃ g : ℂ → ℂ,AnalyticAt ℂ g 0 ∧ g 0=0 ∧
    (∀ᶠ z in 𝓝 (0:ℂ),infinityEquation L (z,g z)=0) ∧
    (∀ᶠ v in 𝓝 ((0,0):ℂ × ℂ),infinityEquation L v=0 ↔ g v.1=v.2) := by
  have hd : HasDerivAt (fun y : ℂ => infinityEquation L (0,y)) 1 0 := by
    convert (hasDerivAt_id (0:ℂ)).sub (((hasDerivAt_id (0:ℂ)).pow 3).const_mul (B L)) using 1 <;>
      simp [infinityEquation]
  simpa only [infinityEquation,zero_pow (by decide : 3≠0),zero_pow (by decide : 2≠0),
    mul_zero,zero_mul,sub_zero] using
    AnalyticImplicitGraph318.exists_graph (infinity_analytic L (0,0)) hd one_ne_zero
end OriginalPeriodIndependentGraphs318
