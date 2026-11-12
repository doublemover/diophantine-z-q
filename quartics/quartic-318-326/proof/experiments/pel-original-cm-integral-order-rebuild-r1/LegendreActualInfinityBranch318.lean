module
public import LegendreInfinityBranchGerm318
public import WeierstrassInfinityPointProjection318
public import NormalizedLegendreSchemeProjection318
public section
noncomputable section
namespace LegendreActualInfinityBranch318
open AlgebraicGeometry CategoryTheory Filter
open scoped Topology
open NormalizedLegendreProjectiveModel318 LegendreInfinityBranchGerm318
open ProjectiveLineComplexSchemePoints318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- This point lies on the original completed target, via its native
infinity chart and literal coordinate-ring evaluation. -/
@[expose] def point (l u v : ℂ) (he:equation l u v=0) :
    Spec (CommRingCat.of ℂ) ⟶ model l :=
  WeierstrassInfinityPointProjection318.point (A l) (B l) u v he

lemma normalized_projection (l u v : ℂ) (he:equation l u v=0)
    (hD:denominator l u v≠0) (hE:normalizedDenominator l u v≠0) :
    point l u v he ≫ NormalizedLegendreSchemeProjection318.projection l=
      (chartPoint 0 (reciprocal l u v)).val := by
  have hu : 1+shift l*(u^2/denominator l u v)≠0 := by
    have hx : 1+shift l*(u^2/denominator l u v)=
        normalizedDenominator l u v/denominator l u v := by
      dsimp [normalizedDenominator]
      field_simp [hD]
      <;> ring
    rw [hx]
    exact div_ne_zero hE hD
  change WeierstrassInfinityPointProjection318.point (A l) (B l) u v he ≫
    (WeierstrassXProjection318.xMap (A l) (B l) ≫
      (ProjectiveAffineLine318.iso ℂ 1 (shift l)).hom)=_
  rw [←Category.assoc,WeierstrassInfinityPointProjection318.native_projection _ _ _ _ he hD,
    WeierstrassInfinityPointProjection318.translated_reciprocal _ _ hu]
  have hx : (u^2/denominator l u v)/(1+shift l*(u^2/denominator l u v))=
      reciprocal l u v := by
    dsimp [reciprocal,normalizedDenominator] at *
    field_simp [hD,hE]
    <;> ring
  rw [hx]

/-- A complete native branch germ on the SAME completed Legendre target:
full ambient equation uniqueness, an analytic invertible source coordinate
q with derivative ONE, and the exact original Scheme projection equal to
q squared in the reciprocal t chart. All unit conditions are produced. -/
theorem infinity_branch (l:ℂ) :
    ∃ g q k : ℂ→ℂ,
      AnalyticAt ℂ g 0 ∧ g 0=0 ∧
      (∀ᶠ p in 𝓝 ((0,0):ℂ×ℂ),equation l p.1 p.2=0 ↔ g p.1=p.2) ∧
      AnalyticAt ℂ q 0 ∧ q 0=0 ∧ HasDerivAt q 1 0 ∧
      AnalyticAt ℂ k 0 ∧ k 0=0 ∧
      (fun u=>k (q u)) =ᶠ[𝓝 (0:ℂ)] id ∧
      (fun w=>q (k w)) =ᶠ[𝓝 (0:ℂ)] id ∧
      (∀ᶠ u in 𝓝 (0:ℂ),∃ he:equation l u (g u)=0,
        point l u (g u) he ≫ NormalizedLegendreSchemeProjection318.projection l=
          (chartPoint 0 (q u^2)).val) := by
  obtain ⟨g,hg,h0,he,hunique⟩:=native_graph l
  obtain ⟨q,k,hq,hq0,hqd,hk,hk0,hleft,hright,hsquare⟩:=square_uniformizer l g hg h0
  have hD : ContinuousAt (fun u:ℂ=>denominator l u (g u)) 0 := by
    have h : AnalyticAt ℂ (fun u:ℂ=>denominator l u (g u)) 0 := by
      dsimp [denominator]
      fun_prop
    exact h.continuousAt
  have hE : ContinuousAt (fun u:ℂ=>normalizedDenominator l u (g u)) 0 := by
    have h : AnalyticAt ℂ (fun u:ℂ=>normalizedDenominator l u (g u)) 0 := by
      dsimp [normalizedDenominator,denominator]
      fun_prop
    exact h.continuousAt
  have hD0 : denominator l 0 (g 0)≠0 := by simp [denominator,h0]
  have hE0 : normalizedDenominator l 0 (g 0)≠0 := by
    simp [normalizedDenominator,denominator,h0]
  have hDn : ∀ᶠ u in 𝓝 (0:ℂ),denominator l u (g u)≠0 := hD.eventually_ne hD0
  have hEn : ∀ᶠ u in 𝓝 (0:ℂ),normalizedDenominator l u (g u)≠0 := hE.eventually_ne hE0
  refine ⟨g,q,k,hg,h0,hunique,hq,hq0,hqd,hk,hk0,hleft,hright,?_⟩
  filter_upwards [he,hsquare,hDn,hEn] with u hu hs hd hn
  refine ⟨hu,?_⟩
  rw [normalized_projection l u (g u) hu hd hn,hs]
end LegendreActualInfinityBranch318
