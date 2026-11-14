module
public import LegendreSimpleBranchCharts318
public import LocalHolomorphicSquareRoot318
public section
noncomputable section
namespace LegendreInfinityBranchGerm318
open Filter Set
open scoped Topology
open NormalizedLegendreProjectiveModel318
set_option maxHeartbeats 1200000

/-- Literal native infinity plane, with U=x/y and V=1/y for the SAME
translated short Weierstrass model. -/
@[expose] def equation (l : ℂ) (u v : ℂ) : ℂ :=
  v-u^3-A l*u*v^2-B l*v^3
@[expose] def denominator (l u v : ℂ) : ℂ := 1-A l*u*v-B l*v^2
/-- The target is reciprocal ORIGINAL t=x+shift, not reciprocal native x. -/
@[expose] def normalizedDenominator (l u v : ℂ) : ℂ :=
  denominator l u v+shift l*u^2
@[expose] def reciprocal (l u v : ℂ) : ℂ := u^2/normalizedDenominator l u v

lemma equation_identity (l u v : ℂ) (h : equation l u v=0) :
    v*denominator l u v=u^3 := by
  dsimp [equation] at h
  dsimp [denominator]
  linear_combination h
lemma normalized_identity (l u v : ℂ) (h : equation l u v=0) :
    v*normalizedDenominator l u v=u^2*(u+shift l*v) := by
  have he:=equation_identity l u v h
  dsimp [normalizedDenominator]
  linear_combination he

/-- Actual full implicit native chart near infinity; includes ambient
uniqueness, not just one parametrized family on the equation. -/
theorem native_graph (l : ℂ) :
    ∃ g : ℂ→ℂ, AnalyticAt ℂ g 0 ∧ g 0=0 ∧
      (∀ᶠ u in 𝓝 (0:ℂ),equation l u (g u)=0) ∧
      (∀ᶠ p in 𝓝 ((0,0):ℂ×ℂ),equation l p.1 p.2=0 ↔ g p.1=p.2) := by
  let f : ℂ×ℂ→ℂ := fun p=>equation l p.1 p.2
  have hf : AnalyticAt ℂ f (0,0) := by dsimp [f,equation]; fun_prop
  have hd : HasDerivAt (fun v:ℂ=>f (0,v)) 1 0 := by
    convert ((hasDerivAt_id (0:ℂ)).sub
      ((hasDerivAt_const (0:ℂ) (B l)).mul ((hasDerivAt_id (0:ℂ)).pow 3))) using 1 <;>
      simp [f,equation]
  obtain ⟨g,hg,h0,he,hu⟩:=AnalyticImplicitGraph318.exists_graph hf hd one_ne_zero
  have hz : f (0,0)=0 := by simp [f,equation]
  rw [hz] at he hu
  exact ⟨g,hg,h0,he,hu⟩

/-- A true square-root uniformizer for the SAME normalized projection at
infinity. The coordinate has derivative ONE, so it is genuinely invertible.
No pole-order assertion is substituted for an analytic inverse. -/
theorem square_uniformizer (l : ℂ) (g : ℂ→ℂ)
    (hg : AnalyticAt ℂ g 0) (h0 : g 0=0) :
    ∃ q k : ℂ→ℂ, AnalyticAt ℂ q 0 ∧ q 0=0 ∧ HasDerivAt q 1 0 ∧
      AnalyticAt ℂ k 0 ∧ k 0=0 ∧
      (fun u=>k (q u)) =ᶠ[𝓝 (0:ℂ)] id ∧
      (fun w=>q (k w)) =ᶠ[𝓝 (0:ℂ)] id ∧
      (∀ᶠ u in 𝓝 (0:ℂ),q u^2=reciprocal l u (g u)) := by
  let E : ℂ→ℂ := fun u=>normalizedDenominator l u (g u)
  have hE : AnalyticAt ℂ E 0 := by
    dsimp [E,normalizedDenominator,denominator]
    fun_prop
  have hE0 : E 0=1 := by simp [E,normalizedDenominator,denominator,h0]
  obtain ⟨s,hs,hs0,hsq⟩:=LocalHolomorphicSquareRoot318.exists_local_root E 0 1 hE
    (by rw [hE0]; exact one_ne_zero) (by rw [hE0]; norm_num)
  let q : ℂ→ℂ := fun u=>u/s u
  have hq : AnalyticAt ℂ q 0 := analyticAt_id.div hs (by rw [hs0]; exact one_ne_zero)
  have hq0 : q 0=0 := by simp [q]
  have hqd : HasDerivAt q 1 0 := by
    have h:=(hasDerivAt_id (0:ℂ)).div hs.differentiableAt.hasDerivAt
      (by rw [hs0]; exact one_ne_zero)
    simpa [q,hs0] using h
  obtain ⟨k,hk,hk0,hleft,hright⟩:=FiniteAnalyticCharts318.analytic_inverse hq
    (by rw [hqd.deriv]; exact one_ne_zero)
  rw [hq0] at hk hk0 hright
  refine ⟨q,k,hq,hq0,hqd,hk,hk0,hleft,hright,?_⟩
  filter_upwards [] with u
  change (u/s u)^2=u^2/E u
  rw [div_pow,hsq]
end LegendreInfinityBranchGerm318
