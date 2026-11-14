module
public import FourRootCompletedComplexAtlas318
public import ComplexSphereAffineNormalization318
public section
noncomputable section
namespace FourRootCompletedHausdorff318
open Set Filter FourRootNormalizedPointCharts318 FourRootGluedTopology318
open ComplexSphereAffineNormalization318 SphereInversion318
open scoped Topology OnePoint
variable (b:Fin 4→ℂ)
local instance : TopologicalSpace (Completed b):=topology b

/-- Exact sphere-valued infinity formula includes u=0. This supplies
continuity across all eight infinity centers, not just on the overlap. -/
lemma infinity_projection (q:InfinityPoints b):
    projection b (FourRootNormalizedPointCharts318.infinityChart b q)=
      affineSphere 1 (b 0) one_ne_zero (inversion (q.val.1^2:ℂ)) := by
  by_cases h:q.val.1=0
  · rw [FourRootNormalizedPointCharts318.infinityChart,dif_pos h]
    change ∞=affineSphere 1 (b 0) one_ne_zero (inversion (q.val.1^2:ℂ))
    rw [h,zero_pow (by decide:2≠0),inversion_zero,affineSphere_infty]
  · rw [infinity_projection_nonzero b q h,inversion_coe (pow_ne_zero 2 h),affineSphere_coe]
    congr 1
    ring

theorem projection_continuous : Continuous (projection b) := by
  apply (FourRootGluedTopology318.continuous_iff b (projection b)).mpr
  constructor
  · exact OnePoint.continuous_coe.comp continuous_subtype_val.fst
  · have he:(projection b ∘ FourRootNormalizedPointCharts318.infinityChart b)=
        fun q:InfinityPoints b=>affineSphere 1 (b 0) one_ne_zero (inversion (q.val.1^2:ℂ)):=
      funext (infinity_projection b)
    rw [he]
    exact (affineSphere 1 (b 0) one_ne_zero).continuous.comp
      (inversion_continuous.comp (OnePoint.continuous_coe.comp
        (continuous_subtype_val.fst.pow 2)))

private theorem separate_open_embedding {X Y:Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space X] (f:X→Y) (hf:Topology.IsOpenEmbedding f)
    (x y:X) (hne:f x≠f y):
    ∃U V:Set Y,IsOpen U ∧ IsOpen V ∧ f x∈U ∧ f y∈V ∧ Disjoint U V:=by
  obtain ⟨U,V,hU,hV,hx,hy,hd⟩:=t2_separation (show x≠y from fun h=>hne (congrArg f h))
  refine ⟨f '' U,f '' V,hf.isOpenMap U hU,hf.isOpenMap V hV,
    ⟨x,hx,rfl⟩,⟨y,hy,rfl⟩,?_⟩
  apply Set.disjoint_left.mpr
  rintro z ⟨a,ha,he⟩ ⟨c,hc,hf'⟩
  have hac:a=c:=hf.injective (he.trans hf'.symm)
  exact Set.disjoint_left.mp hd ha (hac.symm ▸ hc)

private theorem separate_projection (x y:Completed b) (hne:projection b x≠projection b y):
    ∃U V:Set (Completed b),IsOpen U ∧ IsOpen V ∧ x∈U ∧ y∈V ∧ Disjoint U V:=by
  obtain ⟨U,V,hU,hV,hx,hy,hd⟩:=t2_separation hne
  exact ⟨projection b ⁻¹' U,projection b ⁻¹' V,
    hU.preimage (projection_continuous b),hV.preimage (projection_continuous b),hx,hy,
    hd.preimage (projection b)⟩

/-- Hausdorffness is proved in the independent glued topology. Finite
pairs share one affine chart; infinity pairs share the normalized chart;
mixed pairs are separated by their actual continuous sphere projection. -/
theorem hausdorff : T2Space (Completed b):=by
  refine ⟨?_⟩
  intro x y hne
  rcases x with p|s <;> rcases y with q|t
  · exact separate_open_embedding (FourRootNormalizedPointCharts318.finiteChart b)
      (finite_openEmbedding b) p q hne
  · exact separate_projection b _ _ (OnePoint.coe_ne_infty _)
  · exact separate_projection b _ _ (Ne.symm (OnePoint.coe_ne_infty _))
  · have hs:FourRootNormalizedPointCharts318.infinityChart b (FourRootInfinityGraph318.center b s)=Sum.inr s:=
      infinityChart_zero b s
    have ht:FourRootNormalizedPointCharts318.infinityChart b (FourRootInfinityGraph318.center b t)=Sum.inr t:=
      infinityChart_zero b t
    obtain ⟨U,V,hU,hV,hx,hy,hd⟩:=separate_open_embedding
      (FourRootNormalizedPointCharts318.infinityChart b) (infinity_openEmbedding b)
      (FourRootInfinityGraph318.center b s) (FourRootInfinityGraph318.center b t)
      (by simpa only [hs,ht] using hne)
    exact ⟨U,V,hU,hV,hs ▸ hx,ht ▸ hy,hd⟩
end FourRootCompletedHausdorff318
