module
public import PuncturedSquareCoordinate318
public import LegendreLiteralFiniteBranch318
public section
noncomputable section
namespace LegendrePuncturedFiniteExtension318
open Set Filter
open scoped Topology
open LegendreHalfPlaneAnalyticSheets318 LegendreSimpleBranchCharts318

/-- A map into the literal original Legendre equation with SAME source
projection t=a+w² extends across its branch point by an invertible local
coordinate. Its target chart membership and continuity are conclusions;
no choice of an analytic sign on a punctured disc is assumed. -/
theorem extend (l:ℂ) (h0:l≠0) (h1:l≠1) (j:Fin 3) (y:ℂ→ℂ)
    (hy:∀ᶠ w in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ y w)
    (he:∀ᶠ w in 𝓝[≠] (0:ℂ),y w^2=polynomial l (branch l j+w^2)) :
    ∃q k:ℂ→ℂ,AnalyticAt ℂ q 0 ∧ q 0=0 ∧ deriv q 0^2=1 ∧
      AnalyticAt ℂ k 0 ∧ k 0=0 ∧
      (fun w=>k (q w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (fun w=>q (k w))=ᶠ[𝓝 (0:ℂ)] id ∧
      (∀ᶠ w in 𝓝 (0:ℂ),q w^2=w^2) ∧
      AnalyticAt ℂ (fun w=>(LegendreLiteralFiniteBranch318.point l h0 h1 j (q w)).val) 0 ∧
      (∀ᶠ w in 𝓝[≠] (0:ℂ),
        (LegendreLiteralFiniteBranch318.point l h0 h1 j (q w)).val=
          (branch l j+w^2,y w)) := by
  let a:=branch l j
  let h:=LegendreLiteralFiniteBranch318.root l h0 h1 j
  let t:ℂ→ℂ:=fun w=>a+w^2
  have ht:AnalyticAt ℂ t 0:=analyticAt_const.add (analyticAt_id.pow 2)
  have ht0:t 0=a:=by simp [t]
  have hh:AnalyticAt ℂ h a:=LegendreLiteralFiniteBranch318.root_analytic l h0 h1 j
  have hh0:h a≠0:=LegendreLiteralFiniteBranch318.root_center_ne l h0 h1 j
  have hht:AnalyticAt ℂ (fun w=>h (t w)) 0:=by
    have hh':AnalyticAt ℂ h (t 0):=ht0.symm ▸ hh
    exact hh'.comp ht
  have hu:∀ᶠ w in 𝓝 (0:ℂ),h (t w)≠0:=
    hht.continuousAt.eventually_ne (by simpa only [ht0] using hh0)
  let f:ℂ→ℂ:=fun w=>y w/h (t w)
  have hfd:∀ᶠ w in 𝓝[≠] (0:ℂ),DifferentiableAt ℂ f w:=by
    filter_upwards [hy,hht.eventually_analyticAt.filter_mono nhdsWithin_le_nhds,
      hu.filter_mono nhdsWithin_le_nhds] with w hw ha hn
    exact hw.div ha.differentiableAt hn
  have hfs:∀ᶠ w in 𝓝[≠] (0:ℂ),f w^2=w^2:=by
    filter_upwards [he,hu.filter_mono nhdsWithin_le_nhds] with w hw hn
    have hc:LegendreLiteralFiniteBranch318.cofactor l j (t w)≠0:=by
      rw [←LegendreLiteralFiniteBranch318.root_square l h0 h1 j (t w)]
      exact pow_ne_zero 2 hn
    change (y w/h (t w))^2=w^2
    rw [div_pow,show y w^2=polynomial l (t w) from hw,
      LegendreLiteralFiniteBranch318.root_square,
      LegendreLiteralFiniteBranch318.factorization]
    change ((a+w^2)-a)*LegendreLiteralFiniteBranch318.cofactor l j (t w)/
      LegendreLiteralFiniteBranch318.cofactor l j (t w)=w^2
    rw [add_sub_cancel_left,mul_div_cancel_right₀ _ hc]
  obtain ⟨q,k,hq,hq0,hqf,hqd,hk,hk0,hleft,hright,hqs⟩:=
    PuncturedSquareCoordinate318.extend f hfd hfs
  have hpoint:AnalyticAt ℂ (fun w=>(LegendreLiteralFiniteBranch318.point l h0 h1 j (q w)).val) 0:=by
    have hp:=LegendreLiteralFiniteBranch318.point_coordinates_analytic l h0 h1 j
    have hp':AnalyticAt ℂ (fun v=>(LegendreLiteralFiniteBranch318.point l h0 h1 j v).val) (q 0):=
      hq0.symm ▸ hp
    exact hp'.comp hq
  refine ⟨q,k,hq,hq0,hqd,hk,hk0,hleft,hright,hqs,hpoint,?_⟩
  filter_upwards [hqf,hqs.filter_mono nhdsWithin_le_nhds,
    hu.filter_mono nhdsWithin_le_nhds] with w hqfw hqsw hunit
  apply Prod.ext
  · change a+q w^2=a+w^2
    rw [hqsw]
  · change q w*h (a+q w^2)=y w
    rw [hqsw,hqfw]
    exact div_mul_cancel₀ _ hunit
end LegendrePuncturedFiniteExtension318
