module
public import PELOriginalInvolutionUnramified318
public section
noncomputable section
namespace OriginalLocalSquareObstruction318
open Filter Topology
set_option maxHeartbeats 2000000
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- An exact local square at its zero cannot agree with an injective map
on ANY open neighborhood. This checks ramification from genuine coordinates,
not a deficient finite fiber count. -/
theorem not_injective_neighborhood (f : X→Y) (p : X)
    (e : OpenPartialHomeomorph X ℂ) (b : OpenPartialHomeomorph Y ℂ)
    (hp : p∈e.source) (he0 : e p=0)
    (hmodel : ∀ x∈e.source,f x∈b.source ∧ b (f x)=(e x)^2)
    (U : Set X) (hU : IsOpen U) (hpU : p∈U) : ¬ Set.InjOn f U := by
  intro hi
  have hW : IsOpen (e '' (U∩e.source)) :=
    e.isOpen_image_of_subset_source (hU.inter e.open_source) (fun _ hx => hx.2)
  have h0 : (0:ℂ)∈e '' (U∩e.source) := ⟨p,⟨hpU,hp⟩,he0⟩
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds h0)
  let z : ℂ := (r/2:ℝ)
  have hn : ‖z‖=r/2 := by simp [z,Real.norm_eq_abs,abs_of_pos (half_pos hr)]
  have hz : z∈Metric.ball (0:ℂ) r := by
    rw [Metric.mem_ball,dist_zero_right,hn]
    linarith
  have hmz : -z∈Metric.ball (0:ℂ) r := by
    rw [Metric.mem_ball,dist_zero_right,norm_neg,hn]
    linarith
  obtain ⟨x,hx,hex⟩ := hball hz
  obtain ⟨y,hy,hey⟩ := hball hmz
  have hfx : f x=f y := by
    apply b.injOn (hmodel x hx.2).1 (hmodel y hy.2).1
    rw [(hmodel x hx.2).2,(hmodel y hy.2).2,hex,hey]
    ring
  have he : z=-z := hex.symm.trans ((congrArg e (hi hx.1 hy.1 hfx)).trans hey)
  have hz0 : z=0 := by
    have htwo : (2:ℂ)*z=0 := by linear_combination he
    exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)
  have hn0 : r/2=0 := by rw [←hn,hz0,norm_zero]
  linarith
end OriginalLocalSquareObstruction318
