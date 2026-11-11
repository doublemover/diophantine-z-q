module
public import ContinuousMonicRootQuotient318
public import Mathlib.FieldTheory.Separable
public section
noncomputable section
namespace LocallyUniqueMonicRootSimple318
open Set Filter Polynomial ContinuousMonicRootQuotient318
open scoped Topology
variable {E : Type*} [TopologicalSpace E]

/-- A continuous branch that exhausts ALL nearby roots of a generically
separable fixed-degree monic family is simple at its center. Residual
root continuity retains multiplicities, so no ramification is silently
discarded at the point being tested. -/
theorem derivative_ne_zero (p : E → Polynomial ℂ) (N : ℕ)
    (hm : ∀ y, (p y).Monic) (hd : ∀ y, (p y).natDegree = N)
    (hp : ∀ k, Continuous (fun y => (p y).coeff k))
    (b : E → ℂ) (hb : Continuous b) (hroot : ∀ y, (p y).IsRoot (b y))
    (hs : Dense {y : E | (p y).Separable})
    (x : E) (U : Set (E × ℂ)) (hU : IsOpen U) (hx : (x,b x) ∈ U)
    (hunique : ∀ y z, (y,z) ∈ U → (p y).IsRoot z → z = b y) :
    (p x).derivative.eval (b x) ≠ 0 := by
  intro hzero
  let q := quotient p b
  have hqroot : (q x).IsRoot (b x) := by
    change (quotient p b x).eval (b x) = 0
    rw [value_eq_derivative p b hroot,hzero]
  have hnear := MonicRootProjectionOpen318.eventually_root_mem q (N-1)
    (monic p b hm hroot) (degree p b N hd)
    (evaluation_continuous p b N hd hp hb) x (b x) hqroot U hU hx
  have hbad : ∀ᶠ y in 𝓝 x, (p y).derivative.eval (b y) = 0 := by
    filter_upwards [hnear] with y hy
    obtain ⟨z,hz,hyz⟩ := hy
    have he : z = b y := hunique y z hyz (root_of_quotient_root p b hroot y z hz)
    rw [he] at hz
    change (quotient p b y).eval (b y) = 0 at hz
    rwa [value_eq_derivative p b hroot] at hz
  obtain ⟨V,hV,hVo,hxV⟩ := mem_nhds_iff.mp hbad
  obtain ⟨y,hyV,hys⟩ := hs.inter_open_nonempty V hVo ⟨x,hxV⟩
  have hn := hys.aeval_derivative_ne_zero
    (by simpa only [Polynomial.aeval_def,Polynomial.eval₂_id] using (hroot y))
  exact hn (by simpa only [Polynomial.aeval_def,Polynomial.eval₂_id] using hV hyV)
end LocallyUniqueMonicRootSimple318
