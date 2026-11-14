module
public import BoundedVertexExtension318
public section
noncomputable section
namespace ComplexCurveFiniteFilling318
open Set Filter Function
open scoped Topology Manifold ContDiff
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000
variable {M N : Type*} [TopologicalSpace M] [TopologicalSpace N] [T1Space M]

/-- Fill only the specified finite exceptional points with their constructed
limits. All original values away from the exception set are retained. -/
@[expose] def fill (S : Set M) (F a : M → N) (p : M) : N :=
  if p∈S then a p else F p

lemma away_eventually (S : Set M) (hS : S.Finite) (F a : M → N)
    {p : M} (hp : p∉S) : fill S F a =ᶠ[𝓝 p] F := by
  filter_upwards [hS.isClosed.isOpen_compl.mem_nhds hp] with q hq
  exact if_neg hq

/-- Punctured limits provide continuity of the filled map at every
exceptional point. No target compactness or assumed boundary continuity. -/
theorem continuous_fill (S : Set M) (hS : S.Finite) (F a : M → N)
    (hF : ∀ p∉S,ContinuousAt F p)
    (hlim : ∀ p∈S,Tendsto F (𝓝[≠] p) (𝓝 (a p))) : Continuous (fill S F a) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  by_cases hp : p∈S
  · have hc : ContinuousAt (update F p (a p)) p :=
      continuousAt_update_same.mpr (hlim p hp)
    apply hc.congr_of_eventuallyEq
    have hfinite : (S\{p}).Finite := hS.subset diff_subset
    have hnb : (S\{p})ᶜ∈𝓝 p := hfinite.isClosed.isOpen_compl.mem_nhds (by simp)
    filter_upwards [hnb] with q hq
    by_cases hqp : q=p
    · subst q
      simp only [fill,if_pos hp,Function.update_self]
    · have hqS : q∉S := fun hs => hq ⟨hs,hqp⟩
      simp only [fill,if_neg hqS,update_of_ne hqp]
  · exact (hF p hp).congr_of_eventuallyEq (away_eventually S hS F a hp)

variable [ChartedSpace ℂ M] [ChartedSpace ℂ N]
    [IsManifold 𝓘(ℂ,ℂ) ω M] [IsManifold 𝓘(ℂ,ℂ) ω N]

/-- The actual complex-curve map extends globally and holomorphically
from a finite puncture set once its genuine punctured limits are produced.
It agrees with the original map at EVERY nonexceptional point. -/
theorem holomorphic_fill (S : Set M) (hS : S.Finite) (F a : M → N)
    (hF : ∀ p∉S,ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω F p)
    (hlim : ∀ p∈S,Tendsto F (𝓝[≠] p) (𝓝 (a p))) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (fill S F a) ∧
      ∀ p∉S,fill S F a p=F p := by
  refine ⟨?_,fun p hp => if_neg hp⟩
  apply ComplexCurveRemovablePoints318.holomorphic_of_finite_exception
    (fill S F a) (continuous_fill S hS F a (fun p hp => (hF p hp).continuousAt) hlim) S hS
  intro p hp
  exact (hF p hp).congr_of_eventuallyEq (away_eventually S hS F a hp)
end ComplexCurveFiniteFilling318
