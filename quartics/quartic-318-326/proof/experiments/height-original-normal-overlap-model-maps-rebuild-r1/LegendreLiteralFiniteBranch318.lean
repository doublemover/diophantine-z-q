module
public import LegendreSimpleBranchCharts318
public import LocalHolomorphicSquareRoot318
public section
noncomputable section
namespace LegendreLiteralFiniteBranch318
open Set Filter
open scoped Topology
open LegendreHalfPlaneAnalyticSheets318 LegendreSimpleBranchCharts318
open NormalizedLegendreFieldPoints318
set_option maxHeartbeats 1200000

/-- The original cubic, divided by the SPECIFIED simple branch factor. -/
@[expose] def cofactor (l:ℂ) : Fin 3→ℂ→ℂ :=
  ![fun t=>(t-1)*(t-l),fun t=>t*(t-l),fun t=>t*(t-1)]
lemma factorization (l t:ℂ) (j:Fin 3) :
    polynomial l t=(t-branch l j)*cofactor l j t := by
  fin_cases j <;> dsimp [polynomial,branch,cofactor] <;> ring
lemma cofactor_center (l:ℂ) (j:Fin 3) : cofactor l j (branch l j)=slope l (branch l j) := by
  fin_cases j <;> dsimp [branch,cofactor,slope] <;> ring
lemma cofactor_analytic (l:ℂ) (j:Fin 3) (t:ℂ) : AnalyticAt ℂ (cofactor l j) t := by
  fin_cases j <;> dsimp [cofactor] <;> fun_prop

/-- Construct a holomorphic unit square root through the chosen original
branch factor. Its global square identity defines actual points for every
parameter; analyticity is claimed only on the genuine local neighborhood. -/
theorem unit_root (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) :
    ∃h:ℂ→ℂ,AnalyticAt ℂ h (branch l j) ∧ h (branch l j)≠0 ∧
      ∀t,h t^2=cofactor l j t := by
  have hc:cofactor l j (branch l j)≠0:=by
    rw [cofactor_center]
    exact branch_slope_nonzero l h0 h1 j
  let b:=Complex.sqrt (cofactor l j (branch l j))
  have hb:b^2=cofactor l j (branch l j):=LocalHolomorphicSquareRoot318.sqrt_square _
  obtain ⟨h,hh,hb0,he⟩:=LocalHolomorphicSquareRoot318.exists_local_root
    (cofactor l j) (branch l j) b (cofactor_analytic l j _) hc hb
  refine ⟨h,hh,?_,he⟩
  intro hz
  apply hc
  rw [←he (branch l j),hz,zero_pow (by decide : 2≠0)]

@[expose] def root (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) : ℂ→ℂ:=
  (unit_root l h0 h1 j).choose
lemma root_analytic (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) :
    AnalyticAt ℂ (root l h0 h1 j) (branch l j):=(unit_root l h0 h1 j).choose_spec.1
lemma root_center_ne (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) :
    root l h0 h1 j (branch l j)≠0:=(unit_root l h0 h1 j).choose_spec.2.1
lemma root_square (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) (t:ℂ) :
    root l h0 h1 j t^2=cofactor l j t:=(unit_root l h0 h1 j).choose_spec.2.2 t

/-- Literal t=a+w², y=w*h(a+w²), on the SAME finite Legendre equation. -/
@[expose] def point (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) (w:ℂ) : FinitePoints l :=
  ⟨(branch l j+w^2,w*root l h0 h1 j (branch l j+w^2)),by
    rw [mul_pow,root_square,factorization]
    simp only [add_sub_cancel_left]⟩
lemma point_coordinates_analytic (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) :
    AnalyticAt ℂ (fun w=>(point l h0 h1 j w).val) 0 := by
  have ht:AnalyticAt ℂ (fun w:ℂ=>branch l j+w^2) 0:=analyticAt_const.add (analyticAt_id.pow 2)
  have hh:AnalyticAt ℂ (root l h0 h1 j) (branch l j+(0:ℂ)^2):=by
    simpa using root_analytic l h0 h1 j
  exact ht.prod (analyticAt_id.mul (hh.comp ht))
@[expose] def inverse (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) (p:ℂ×ℂ) : ℂ :=
  p.2/root l h0 h1 j p.1
lemma inverse_analytic (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) :
    AnalyticAt ℂ (inverse l h0 h1 j) (branch l j,0) :=
  analyticAt_snd.div ((root_analytic l h0 h1 j).comp analyticAt_fst)
    (root_center_ne l h0 h1 j)
lemma left_inverse (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) :
    (fun w=>inverse l h0 h1 j (point l h0 h1 j w).val) =ᶠ[𝓝 (0:ℂ)] id := by
  have ht:ContinuousAt (fun w:ℂ=>branch l j+w^2) 0:=by fun_prop
  have hh:∀ᶠ w in 𝓝 (0:ℂ),root l h0 h1 j (branch l j+w^2)≠0:=by
    have hn:∀ᶠ t in 𝓝 (branch l j),root l h0 h1 j t≠0:=
      (root_analytic l h0 h1 j).continuousAt.eventually_ne (root_center_ne l h0 h1 j)
    exact ht.eventually (by simpa using hn)
  filter_upwards [hh] with w hw
  exact mul_div_cancel_right₀ w hw

/-- Full ambient right inverse at every nearby point of the original
equation, not merely injectivity of the parametrized family. -/
lemma right_inverse (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) :
    ∀ᶠ p in 𝓝 ((branch l j,0):ℂ×ℂ),
      p.2^2=polynomial l p.1 →
        (point l h0 h1 j (inverse l h0 h1 j p)).val=p := by
  have hh:∀ᶠ p in 𝓝 ((branch l j,0):ℂ×ℂ),root l h0 h1 j p.1≠0:=
    continuousAt_fst.eventually
      ((root_analytic l h0 h1 j).continuousAt.eventually_ne (root_center_ne l h0 h1 j))
  filter_upwards [hh] with p hp he
  have hc:cofactor l j p.1≠0:=by rw [←root_square l h0 h1 j p.1];exact pow_ne_zero 2 hp
  have hw:inverse l h0 h1 j p^2=p.1-branch l j:=by
    rw [inverse,div_pow,he,root_square,factorization]
    exact mul_div_cancel_right₀ _ hc
  apply Prod.ext
  · change branch l j+inverse l h0 h1 j p^2=p.1
    rw [hw]
    ring
  · change inverse l h0 h1 j p*root l h0 h1 j (branch l j+inverse l h0 h1 j p^2)=p.2
    have ht:branch l j+inverse l h0 h1 j p^2=p.1:=by rw [hw];ring
    rw [ht,inverse]
    exact div_mul_cancel₀ _ hp
lemma exact_projection (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) (w:ℂ) :
    NormalizedLegendreFiniteProjection318.project l
      (schemeEquiv l (some (point l h0 h1 j w)))=
        ProjectiveLineComplexSchemePoints318.chartPoint 1 (branch l j+w^2) :=
  NormalizedLegendreFiniteProjection318.finite_projection l _
end LegendreLiteralFiniteBranch318
