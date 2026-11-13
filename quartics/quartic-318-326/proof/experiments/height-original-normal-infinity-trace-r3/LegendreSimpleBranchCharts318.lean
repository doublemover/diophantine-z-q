module
public import LegendreHalfPlaneAnalyticSheets318
public import AnalyticImplicitGraph318
public section
noncomputable section
namespace LegendreSimpleBranchCharts318
open Set Filter
open scoped Topology
open LegendreHalfPlaneAnalyticSheets318 NormalizedLegendreFieldPoints318
set_option maxHeartbeats 1200000

@[expose] def branch (l:ℂ) : Fin 3→ℂ:=![0,1,l]
@[expose] def slope (l z:ℂ) : ℂ:=3*z^2-2*(l+1)*z+l
lemma polynomial_derivative (l z:ℂ) : HasDerivAt (polynomial l) (slope l z) z := by
  convert (((hasDerivAt_id z).mul ((hasDerivAt_id z).sub_const 1)).mul
    ((hasDerivAt_id z).sub_const l)) using 1 <;> dsimp [polynomial,slope] <;> ring
lemma branch_zero (l:ℂ) (j:Fin 3) : polynomial l (branch l j)=0 := by
  fin_cases j <;> simp [branch,polynomial]
lemma branch_slope_nonzero (l:ℂ) (hl0:l≠0) (hl1:l≠1) (j:Fin 3) :
    slope l (branch l j)≠0 := by
  fin_cases j
  · simpa [branch,slope] using hl0
  · have h: slope l (branch l 1)=1-l:=by simp [branch,slope];ring
    rw [h]
    exact sub_ne_zero.mpr hl1.symm
  · have h: slope l (branch l 2)=l*(l-1):=by simp [branch,slope];ring
    rw [h]
    exact mul_ne_zero hl0 (sub_ne_zero.mpr hl1)

/-- At each actual finite branch value the SAME base polynomial has an
analytic inverse germ, so it is a genuine base coordinate, not merely a
function vanishing there. Its derivative nonvanishing is explicit. -/
theorem base_coordinate_inverse (l:ℂ) (hl0:l≠0) (hl1:l≠1) (j:Fin 3) :
    ∃g:ℂ→ℂ,AnalyticAt ℂ g 0 ∧ g 0=branch l j ∧
      (fun t=>g (polynomial l t)) =ᶠ[𝓝 (branch l j)] id ∧
      (fun w=>polynomial l (g w)) =ᶠ[𝓝 (0:ℂ)] id := by
  have ha:=polynomial_analytic l (branch l j) (mem_univ _)
  have hd:deriv (polynomial l) (branch l j)≠0:=by
    rw [(polynomial_derivative l (branch l j)).deriv]
    exact branch_slope_nonzero l hl0 hl1 j
  obtain ⟨g,hg,hv,hleft,hright⟩:=FiniteAnalyticCharts318.analytic_inverse ha hd
  rw [branch_zero] at hg hv hright
  exact ⟨g,hg,hv,hleft,hright⟩

/-- Literal finite-equation graph near EACH actual branch point, with
FULL ambient uniqueness. Source parameter is original y and original
projection t is its analytic graph. In the genuine base coordinate P(t),
this SAME projection is exactly y squared. -/
theorem finite_branch_graph (l:ℂ) (hl0:l≠0) (hl1:l≠1) (j:Fin 3) :
    ∃g:ℂ→ℂ,AnalyticAt ℂ g 0 ∧ g 0=branch l j ∧
      (∀ᶠ y in 𝓝 (0:ℂ),y^2=polynomial l (g y)) ∧
      (∀ᶠ v in 𝓝 ((0,branch l j):ℂ×ℂ),v.1^2=polynomial l v.2 ↔ g v.1=v.2) := by
  let f:ℂ×ℂ→ℂ:=fun v=>v.1^2-polynomial l v.2
  have hf:AnalyticAt ℂ f (0,branch l j):=by
    dsimp [f,polynomial]
    fun_prop
  have hd:HasDerivAt (fun t:ℂ=>f (0,t)) (-slope l (branch l j)) (branch l j):=by
    simpa only [f,zero_pow (by decide : 2≠0),zero_sub] using
      (polynomial_derivative l (branch l j)).neg
  obtain ⟨g,hg,hv,he,hu⟩:=AnalyticImplicitGraph318.exists_graph hf hd
    (neg_ne_zero.mpr (branch_slope_nonzero l hl0 hl1 j))
  have hzero:f (0,branch l j)=0:=by simp only [f,zero_pow (by decide : 2≠0),branch_zero,sub_self]
  refine ⟨g,hg,hv,?_,?_⟩
  · filter_upwards [he] with y hy
    change y^2-polynomial l (g y)=_ at hy
    rw [hzero] at hy
    exact sub_eq_zero.mp hy
  · rw [hzero] at hu
    filter_upwards [hu] with v hv
    simpa only [f,sub_eq_zero] using hv

/-- Actual chart points satisfy the original finite Scheme projection
square. No replacement curve is introduced by the implicit graph. -/
theorem graph_scheme_projection (l:ℂ) (g:ℂ→ℂ) (y:ℂ)
    (he:y^2=polynomial l (g y)) :
    NormalizedLegendreFiniteProjection318.project l
      (schemeEquiv l (some ⟨(g y,y),he⟩))=
        ProjectiveLineComplexSchemePoints318.chartPoint 1 (g y) :=
  NormalizedLegendreFiniteProjection318.finite_projection l _
end LegendreSimpleBranchCharts318
