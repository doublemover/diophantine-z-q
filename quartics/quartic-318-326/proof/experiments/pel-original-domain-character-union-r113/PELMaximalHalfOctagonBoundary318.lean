module
public import PELMaximalHalfOctagonCoordinates318
public section
noncomputable section
namespace PELMaximalHalfOctagonBoundary318
open Set Metric Filter
open scoped Topology
open PELMaximalHalfOctagonShape318 PELMaximalHalfOctagonCoordinates318

theorem strict_subset : strictPolygon⊆centeredPolygon := by
  rintro z ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩
  exact ⟨h₁.le,h₂.le,h₃.le,h₄.le,h₅.le,h₆.le⟩

theorem interior_eq_strict : interior centeredPolygon=strictPolygon := by
  apply Set.Subset.antisymm
  · intro z hz
    have hc : Continuous (fun t : ℝ => t • z) := continuous_id.smul continuous_const
    have hn : centeredPolygon∈𝓝 ((1:ℝ) • z) := by
      simpa only [one_smul] using mem_interior_iff_mem_nhds.mp hz
    have ht : {t : ℝ | t • z∈centeredPolygon}∈𝓝 (1:ℝ) :=
      hc.continuousAt.preimage_mem_nhds hn
    obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp ht
    have hdist : (1+ε/2:ℝ)∈ball 1 ε := by
      rw [Metric.mem_ball,Real.dist_eq,abs_of_nonneg (by linarith : 0≤(1+ε/2:ℝ)-1)]
      linarith
    have hext := hball hdist
    change -30≤(1+ε/2)*z.re ∧ (1+ε/2)*z.re≤30 ∧
      -(1/2:ℝ)≤(1+ε/2)*z.im ∧ (1+ε/2)*z.im≤1/2 ∧
      (1+ε/2)*z.re+7*((1+ε/2)*z.im)≤63/2 ∧
      -((1+ε/2)*z.re)+7*((1+ε/2)*z.im)≤63/2 at hext
    obtain ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := hext
    have T (v c : ℝ) (hc : 0<c) (he : (1+ε/2)*v≤c) : v<c := by
      by_contra h
      have hv : 0<v := lt_of_lt_of_le hc (le_of_not_gt h)
      have hp := mul_pos (by linarith : 0<ε/2) hv
      nlinarith
    refine ⟨?_,?_,?_,?_,?_,?_⟩
    · have h := T (-z.re) 30 (by norm_num) (by linarith); linarith
    · exact T z.re 30 (by norm_num) h₂
    · have h := T (-z.im) (1/2) (by norm_num) (by linarith); linarith
    · exact T z.im (1/2) (by norm_num) h₄
    · exact T (z.re+7*z.im) (63/2) (by norm_num) (by nlinarith)
    · exact T (-z.re+7*z.im) (63/2) (by norm_num) (by nlinarith)
  · intro z hz
    exact mem_interior_iff_mem_nhds.mpr
      (Filter.mem_of_superset (strict_open.mem_nhds hz) strict_subset)

theorem boundary_iff_active (z : centeredPolygon) : z.val∈frontier centeredPolygon ↔
    z.val.im= -(1/2:ℝ) ∨ z.val.im=1/2 ∨ z.val.re= -30 ∨ z.val.re=30 ∨
      z.val.re+7*z.val.im=63/2 ∨ -z.val.re+7*z.val.im=63/2 := by
  rw [←closure_sdiff_interior,polygon_closed.closure_eq,interior_eq_strict]
  have ⟨h₁,h₂,h₃,h₄,h₅,h₆⟩ := z.property
  simp only [Set.mem_sdiff,z.property,true_and,strictPolygon,Set.mem_setOf_eq,
    not_and_or,not_lt]
  constructor
  · rintro (h | h | h | h | h | h)
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith)))))
  · rintro (h | h | h | h | h | h)
    · exact Or.inr (Or.inr (Or.inl (by linarith)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (by linarith))))
    · exact Or.inl (by linarith)
    · exact Or.inr (Or.inl (by linarith))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith)))))

/-- Exact original-coordinate boundary, including the cut edge B=0 rather
than only the boundary of the full octagon. -/
theorem cut_boundary_iff (P : upperCut) :
    (upperCutCenter P).val∈frontier centeredPolygon ↔
      P.val.2=0 ∨ P.val.2=1 ∨ P.val.1= -30 ∨ P.val.1=30 ∨
        P.val.1+7*P.val.2=35 ∨ -P.val.1+7*P.val.2=35 := by
  rw [boundary_iff_active]
  change ((centerHomeomorph P.val).im= -(1/2:ℝ) ∨ (centerHomeomorph P.val).im=1/2 ∨
    (centerHomeomorph P.val).re= -30 ∨ (centerHomeomorph P.val).re=30 ∨
    (centerHomeomorph P.val).re+7*(centerHomeomorph P.val).im=63/2 ∨
    -(centerHomeomorph P.val).re+7*(centerHomeomorph P.val).im=63/2) ↔ _
  simp only [centerHomeomorph,Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,mul_zero,zero_mul,sub_zero,add_zero,
    Complex.add_im,Complex.mul_im,mul_one,zero_add]
  constructor <;> rintro (h | h | h | h | h | h)
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith)))))
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by linarith)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by linarith)))))
end PELMaximalHalfOctagonBoundary318
