module
public import InfinityAnalyticChart318
public section
noncomputable section
open Filter Set
open scoped Topology
namespace InfinityBranchUniqueness318
set_option maxHeartbeats 0

@[expose] def equation (A B t v : ℂ) : ℂ := v+t^3+A*t*v^2-B*v^3

lemma difference_factor (A B t v w : ℂ) :
    equation A B t v-equation A B t w =
      (v-w)*(1+A*t*(v+w)-B*(v^2+v*w+w^2)) := by
  unfold equation
  ring

/-- Uniqueness of the actual continuous infinity branch, with no chosen square root. -/
theorem unique_germ (A B : ℂ) (t v w : ℂ → ℂ)
    (ht : ContinuousAt t 0) (hv : ContinuousAt v 0) (hw : ContinuousAt w 0)
    (ht0 : t 0=0) (hv0 : v 0=0) (hw0 : w 0=0)
    (hev : ∀ᶠ z in 𝓝 (0:ℂ), equation A B (t z) (v z)=0)
    (hew : ∀ᶠ z in 𝓝 (0:ℂ), equation A B (t z) (w z)=0) :
    v =ᶠ[𝓝 0] w := by
  have hc : ContinuousAt
      (fun z => 1+A*t z*(v z+w z)-B*((v z)^2+v z*w z+(w z)^2)) 0 := by
    fun_prop
  have hn : ∀ᶠ z in 𝓝 (0:ℂ),
      1+A*t z*(v z+w z)-B*((v z)^2+v z*w z+(w z)^2)≠0 :=
    hc.eventually_ne (by simp [ht0,hv0,hw0])
  filter_upwards [hev,hew,hn] with z hzv hzw hnz
  have he := difference_factor A B (t z) (v z) (w z)
  rw [hzv,hzw,sub_self] at he
  exact sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hnz)

lemma equation_scale (A B : ℂ) (u : ℂˣ) (t v : ℂ) :
    equation ((u:ℂ)^4*A) ((u:ℂ)^6*B)
      ((u:ℂ)⁻¹*t) (((u:ℂ)⁻¹)^3*v) = ((u:ℂ)⁻¹)^3*equation A B t v := by
  unfold equation
  field_simp
  <;> ring

end InfinityBranchUniqueness318
