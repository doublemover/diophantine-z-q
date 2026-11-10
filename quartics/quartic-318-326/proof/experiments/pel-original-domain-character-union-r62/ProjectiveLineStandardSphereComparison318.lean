module
public import ProjectiveLineIndependentComplexAtlas318
public import ComplexCurveHomeomorphInverse318
public section
noncomputable section
namespace ProjectiveLineStandardSphereComparison318
open Set Filter Topology
open scoped OnePoint Manifold ContDiff
open ProjectiveLineComplexSchemePoints318 ProjectiveLineIndependentPointTopology318
open ProjectiveLineIndependentComplexAtlas318 ComplexSphereCharts318 SphereInversion318
local instance : TopologicalSpace SchemePoints:=pointTopology
local instance : ChartedSpace ℂ SchemePoints:=pointCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω SchemePoints:=complex_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

private lemma holomorphic_of_chart (p:OnePoint ℂ) (j:Fin 2)
    (hp:spherePoint p∈(pointChart j).source)
    (hc:ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (pointChart j ∘ spherePoint) p) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω spherePoint p := by
  have hm:pointChart j∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω SchemePoints:=
    IsManifold.subset_maximalAtlas ⟨j,rfl⟩
  apply (contMDiffWithinAt_iff_target_of_mem_maximalAtlas hm hp).mpr
  exact ⟨spherePoint_continuous.continuousAt.continuousWithinAt,hc.contMDiffWithinAt⟩

/-- Holomorphy agrees with the actual finite polynomial evaluation
coordinate [z:1], rather than an atlas transported by the bijection. -/
lemma finite_holomorphic (z:ℂ) :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω spherePoint (z:OnePoint ℂ) := by
  apply holomorphic_of_chart _ 1
  · rw [spherePoint_coe,pointChart_source]
    exact ⟨z,rfl⟩
  · have hm:affine∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=
      IsManifold.subset_maximalAtlas ⟨false,rfl⟩
    apply (contMDiffAt_of_mem_maximalAtlas hm (affine_mem z)).congr_of_eventuallyEq
    filter_upwards [affine.open_source.mem_nhds (affine_mem z)] with p hp
    obtain ⟨w,rfl⟩:=(affine_source ▸ hp)
    exact (pointChart_evaluation 1 w).trans (affine_coe w).symm

/-- Infinity uses the actual reciprocal scheme chart [1:w] and the
independent standard sphere reciprocal coordinate, including w=0. -/
lemma infinity_holomorphic :
    ContMDiffAt 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω spherePoint (∞:OnePoint ℂ) := by
  apply holomorphic_of_chart _ 0
  · rw [spherePoint_infty,pointChart_source]
    exact ⟨0,rfl⟩
  · have hm:reciprocal∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=
      IsManifold.subset_maximalAtlas ⟨true,rfl⟩
    apply (contMDiffAt_of_mem_maximalAtlas hm reciprocal_mem_infty).congr_of_eventuallyEq
    filter_upwards [reciprocal.open_source.mem_nhds reciprocal_mem_infty] with p hp
    have he:p=inversion (reciprocal p:OnePoint ℂ):=by
      simpa only [reciprocal_symm] using (reciprocal.left_inv hp).symm
    change pointChart 0 (spherePoint p)=reciprocal p
    calc
      pointChart 0 (spherePoint p)=pointChart 0 (spherePoint (inversion (reciprocal p:OnePoint ℂ))):=
        congrArg (fun q=>pointChart 0 (spherePoint q)) he
      _=reciprocal p:=by rw [spherePoint_inversion,pointChart_evaluation]

theorem spherePoint_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω spherePoint := by
  intro p
  induction p using OnePoint.rec with
  | infty=>exact infinity_holomorphic
  | coe z=>exact finite_holomorphic z

/-- Genuine biholomorphic comparison with ALL actual complex-valued
points of the fixed Proj projective-line scheme, on its independent
polynomial-chart analytic topology and complex atlas. This is not a
claim of algebraizing an arbitrary arithmetic source curve. -/
theorem sphereSchemeHomeomorph_biholomorphic :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω sphereSchemeHomeomorph ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω sphereSchemeHomeomorph.symm :=
  ⟨spherePoint_holomorphic,
    ComplexCurveHomeomorphInverse318.inverse sphereSchemeHomeomorph spherePoint_holomorphic⟩
end ProjectiveLineStandardSphereComparison318
