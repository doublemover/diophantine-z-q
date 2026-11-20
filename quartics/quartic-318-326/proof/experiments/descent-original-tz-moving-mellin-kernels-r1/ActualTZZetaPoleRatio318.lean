module
public import Mathlib
public section
noncomputable section
namespace ActualTZZetaPoleRatio318
open Filter Set
open scoped Topology

@[expose] def residueFactor (u : ℂ) : ℂ := u*riemannZeta (1+u)

@[expose] def ratio (s t : ℂ) : ℂ :=
  riemannZeta (1+(s+t))/(riemannZeta (1+s)*riemannZeta (1+t))

/-- A single disk around the pole works for every nonzero complex
shift inside it, not just for each fixed frequency separately. -/
theorem residue_uniform (ε : ℝ) (hε : 0<ε) :
    ∃ r>0,∀ u : ℂ,u≠0→‖u‖<r→‖residueFactor u-1‖<ε := by
  obtain ⟨r,hr,H⟩ := (Metric.tendsto_nhdsWithin_nhds.mp riemannZeta_residue_one) ε hε
  refine ⟨r,hr,?_⟩
  intro u hu hn
  have hsub : (1+u:ℂ)-1=u := by ring
  have hs : 1+u ∈ ({1} : Set ℂ)ᶜ := by
    simp only [Set.mem_compl_iff,Set.mem_singleton_iff]
    intro he
    have h₀ := congrArg (fun z : ℂ => z-1) he
    rw [hsub,sub_self] at h₀
    exact hu h₀
  have hd : dist (1+u) (1:ℂ)<r := by
    simpa only [dist_eq_norm,hsub] using hn
  simpa only [dist_eq_norm,hsub,residueFactor] using H hs hd

theorem ratio_factor (s t : ℂ) (hs : s≠0) (ht : t≠0) (hst : s+t≠0)
    (hS : residueFactor s≠0) (hT : residueFactor t≠0) :
    ratio s t=(s*t/(s+t))*(residueFactor (s+t)/(residueFactor s*residueFactor t)) := by
  have hzS : riemannZeta (1+s)≠0 := by
    intro h
    exact hS (by simp [residueFactor,h])
  have hzT : riemannZeta (1+t)≠0 := by
    intro h
    exact hT (by simp [residueFactor,h])
  unfold ratio residueFactor
  field_simp [hs,ht,hst,hzS,hzT] <;> ring

private theorem around_one (A : ℂ) (ε : ℝ) (hε : ε≤1/2) (hA : ‖A-1‖≤ε) :
    (1:ℝ)/2≤‖A‖ ∧ ‖A‖≤3/2 := by
  have hl := norm_sub_le A (A-1)
  have hh : A-(A-1)=1 := by ring
  rw [hh,norm_one] at hl
  have hu := norm_add_le (A-1) (1:ℂ)
  rw [sub_add_cancel,norm_one] at hu
  constructor <;> linarith

/-- Exact relative sensitivity of the pole ratio. This also proves
the nonvanishing of the denominator in the actual near-pole disk. -/
theorem correction_bound (A B C : ℂ) (ε : ℝ) (hε : ε≤1/2)
    (hA : ‖A-1‖≤ε) (hB : ‖B-1‖≤ε) (hC : ‖C-1‖≤ε) :
    ‖A/(B*C)-1‖≤14*ε := by
  have h₀ : 0≤ε := (norm_nonneg _).trans hA
  have hBl := (around_one B ε hε hB).1
  have hCl := (around_one C ε hε hC).1
  have hBu := (around_one B ε hε hB).2
  have hd : (1:ℝ)/4≤‖B*C‖ := by
    rw [norm_mul]
    have H := mul_le_mul hBl hCl (by norm_num : (0:ℝ)≤1/2) (norm_nonneg B)
    norm_num at H ⊢
    exact H
  have hd' : 0<‖B*C‖ := (by norm_num : (0:ℝ)<1/4).trans_le hd
  have hn : B*C≠0 := by
    intro h
    rw [h,norm_zero] at hd'
    exact (lt_irrefl 0) hd'
  have he : A/(B*C)-1=(A-B*C)/(B*C) := by rw [sub_div,div_self hn]
  have hi : A-B*C=((A-1)-(B-1))-B*(C-1) := by ring
  rw [he,norm_div,hi]
  apply (div_le_iff₀ hd').2
  have H : ‖B‖*‖C-1‖≤(3/2)*ε :=
    mul_le_mul hBu hC (norm_nonneg _) (by norm_num)
  calc
    _ ≤ (‖A-1‖+‖B-1‖)+‖B‖*‖C-1‖ := by
      rw [←norm_mul]
      exact (norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)
    _ ≤ (7/2)*ε := by linarith
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hd (show 0≤14*ε by positivity)
      linarith

end ActualTZZetaPoleRatio318
