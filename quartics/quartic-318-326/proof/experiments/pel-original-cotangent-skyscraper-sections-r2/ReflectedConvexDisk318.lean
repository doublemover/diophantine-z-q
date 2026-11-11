module
public import ReflectedDiskJoukowskiTopology318
public import Mathlib.Analysis.Convex.GaugeRescale
public section
noncomputable section
namespace ReflectedConvexDisk318
open Set Metric Filter
open scoped Topology Pointwise
open ReflectedDiskJoukowski318

theorem reflected_involutive (z : ℂ) : reflected (reflected z)=z := by
  simp [reflected]

theorem reflected_smul (a : ℝ) (z : ℂ) : reflected (a • z)=a • reflected z := by
  simp [reflected]

theorem reflected_norm (z : ℂ) : ‖reflected z‖=‖z‖ := by simp [reflected]

theorem gauge_reflected (s : Set ℂ) (hs : ∀ z, reflected z∈s ↔ z∈s) (z : ℂ) :
    gauge s (reflected z)=gauge s z := by
  rw [gauge_def',gauge_def']
  congr 1
  ext r
  simp only [Set.mem_setOf_eq,←reflected_smul,hs]

theorem rescale_reflected (s t : Set ℂ)
    (hs : ∀ z, reflected z∈s ↔ z∈s) (ht : ∀ z, reflected z∈t ↔ z∈t) (z : ℂ) :
    gaugeRescale s t (reflected z)=reflected (gaugeRescale s t z) := by
  rw [gaugeRescale,gauge_reflected s hs,gauge_reflected t ht]
  exact (reflected_smul _ _).symm

variable (s : Set ℂ) (hc : Convex ℝ s) (h0 : s∈𝓝 0) (hb : Bornology.IsBounded s)

@[expose] def normalization : ℂ ≃ₜ ℂ :=
  gaugeRescaleHomeomorph s (ball 0 1) hc h0
    (NormedSpace.isVonNBounded_of_isBounded _ hb)
    (convex_ball 0 1) (Metric.ball_mem_nhds 0 zero_lt_one)
    (NormedSpace.isVonNBounded_ball _ _ _)

theorem normalization_reflected (hs : ∀ z, reflected z∈s ↔ z∈s) (z : ℂ) :
    normalization s hc h0 hb (reflected z)=reflected (normalization s hc h0 hb z) :=
  rescale_reflected s (ball 0 1) hs
    (fun z => by simp only [Metric.mem_ball,dist_zero_right,reflected_norm]) z

theorem normalization_interior : normalization s hc h0 hb '' interior s=ball 0 1 := by
  simpa only [normalization,isOpen_ball.interior_eq] using
    image_gaugeRescaleHomeomorph_interior hc h0
      (NormedSpace.isVonNBounded_of_isBounded _ hb) (convex_ball 0 1)
      (Metric.ball_mem_nhds 0 zero_lt_one) (NormedSpace.isVonNBounded_ball _ _ _)

theorem normalization_closure : normalization s hc h0 hb '' closure s=closedBall 0 1 := by
  simpa only [normalization,closure_ball (0:ℂ) (by norm_num : (1:ℝ)≠0)] using
    image_gaugeRescaleHomeomorph_closure hc h0
      (NormedSpace.isVonNBounded_of_isBounded _ hb) (convex_ball 0 1)
      (Metric.ball_mem_nhds 0 zero_lt_one) (NormedSpace.isVonNBounded_ball _ _ _)

theorem normalization_frontier : normalization s hc h0 hb '' frontier s=sphere 0 1 := by
  rw [←closure_sdiff_interior,Set.image_sdiff (normalization s hc h0 hb).injective,
    normalization_closure,normalization_interior]
  ext z
  simp only [Set.mem_sdiff,Metric.mem_closedBall,Metric.mem_ball,Metric.mem_sphere,not_lt]
  constructor
  · rintro ⟨h₁,h₂⟩; exact le_antisymm h₁ h₂
  · intro h; exact ⟨h.le,h.ge⟩

@[expose] def closedDiskHomeomorph (hclosed : IsClosed s) : s ≃ₜ Disk :=
  (normalization s hc h0 hb).subtype (by
    intro z
    have heq : normalization s hc h0 hb '' s=closedBall 0 1 := by
      simpa only [hclosed.closure_eq] using normalization_closure s hc h0 hb
    constructor
    · intro hz
      have hi := Set.mem_image_of_mem (normalization s hc h0 hb) hz
      rwa [heq] at hi
    · intro hz
      change normalization s hc h0 hb z∈closedBall (0:ℂ) 1 at hz
      rw [←heq] at hz
      obtain ⟨w,hw,he⟩ := hz
      exact (normalization s hc h0 hb).injective he ▸ hw)

theorem normalization_boundary_iff (z : ℂ) :
    normalization s hc h0 hb z∈sphere 0 1 ↔ z∈frontier s := by
  rw [←normalization_frontier s hc h0 hb]
  constructor
  · rintro ⟨w,hw,he⟩
    exact (normalization s hc h0 hb).injective he ▸ hw
  · intro hz
    exact Set.mem_image_of_mem (normalization s hc h0 hb) hz
end ReflectedConvexDisk318
