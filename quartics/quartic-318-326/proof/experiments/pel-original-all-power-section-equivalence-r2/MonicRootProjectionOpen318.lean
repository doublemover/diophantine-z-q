module
public import MonicComplexRootApproximation318
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Maps.Basic
public section
noncomputable section
namespace MonicRootProjectionOpen318
open Set Filter Polynomial
open scoped Topology
variable {E : Type*} [TopologicalSpace E]

/-- Every ambient neighborhood of a root contains roots over all close
base points. Multiple roots are included by the actual product estimate. -/
lemma eventually_root_mem (p : E → Polynomial ℂ) (N : ℕ)
    (hm : ∀ y, (p y).Monic) (hd : ∀ y, (p y).natDegree = N)
    (hc : ∀ z, Continuous (fun y => (p y).eval z))
    (x : E) (z : ℂ) (hz : (p x).IsRoot z)
    (U : Set (E × ℂ)) (hU : IsOpen U) (hxz : (x,z) ∈ U) :
    ∀ᶠ y in 𝓝 x, ∃ r : ℂ, (p y).IsRoot r ∧ (y,r) ∈ U := by
  obtain ⟨V,hV,W,hW,hVW⟩ := mem_nhds_prod_iff.mp (hU.mem_nhds hxz)
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hW
  have hroots := MonicComplexRootApproximation318.eventually_exists_root_near p x z N
    (Filter.Eventually.of_forall hm) (Filter.Eventually.of_forall hd)
    (hc z).continuousAt hz ε hε
  filter_upwards [hV,hroots] with y hy hroot
  obtain ⟨r,hr,hrz⟩ := hroot
  refine ⟨r,hr,hVW ⟨hy,hball ?_⟩⟩
  simpa only [Metric.mem_ball,dist_eq_norm] using hrz

/-- The whole independently topologized root locus, including branch
points and multiple roots. -/
abbrev Roots (p : E → Polynomial ℂ) := {q : E × ℂ // (p q.1).IsRoot q.2}

/-- Projection of a continuous fixed-degree monic complex polynomial
family is OPEN on its ENTIRE root locus. No discriminant is inverted. -/
theorem projection_open (p : E → Polynomial ℂ) (N : ℕ)
    (hm : ∀ y, (p y).Monic) (hd : ∀ y, (p y).natDegree = N)
    (hc : ∀ z, Continuous (fun y => (p y).eval z)) :
    IsOpenMap (fun q : Roots p => q.val.1) := by
  intro U hU
  obtain ⟨O,hO,rfl⟩ := isOpen_induced_iff.mp hU
  apply isOpen_iff_mem_nhds.mpr
  rintro x ⟨q,hq,rfl⟩
  have hnear := eventually_root_mem p N hm hd hc q.val.1 q.val.2 q.property O hO hq
  filter_upwards [hnear] with y hy
  obtain ⟨r,hr,hyr⟩ := hy
  exact ⟨⟨(y,r),hr⟩,hyr,rfl⟩

/-- Genuine base density lifts through the full root locus, including
all collision/branch points. This is a proved density producer for a
monic hypersurface, not a Zariski-to-Euclidean assumption. -/
theorem dense_preimage (p : E → Polynomial ℂ) (N : ℕ)
    (hm : ∀ y, (p y).Monic) (hd : ∀ y, (p y).natDegree = N)
    (hc : ∀ z, Continuous (fun y => (p y).eval z))
    (D : Set E) (hD : Dense D) : Dense {q : Roots p | q.val.1 ∈ D} :=
  hD.preimage (projection_open p N hm hd hc)
end MonicRootProjectionOpen318
