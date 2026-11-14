module
public import PELOriginalCharacterTransition318
public section
noncomputable section
namespace PELOriginalCharacterComplexAtlas318
open PELUnlevelledComplexBase318 PELOriginalCharacterQuotient318 PELOriginalCharacterTopologicalAtlas318
open PELOriginalCharacterChartLift318 PELOriginalCharacterTransition318 Filter Topology
open scoped Manifold ContDiff
set_option maxHeartbeats 1700000
variable (i : Fin 4)
local instance : ChartedSpace ℂ QuaternionicJointPeriodTopology318.HalfPlane :=
  PELPrincipalBaseHolomorphy318.halfPlaneCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω QuaternionicJointPeriodTopology318.HalfPlane :=
  PELPrincipalBaseHolomorphy318.halfPlane_manifold
local instance : ChartedSpace ℂ UnlevelledBase := unlevelledCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω UnlevelledBase := unlevelled_manifold

/-- A genuine Riemann-surface atlas on the literal original character-kernel
quotient, using EXACTLY the preceding topological charts.
This does not assert compactness, genus, algebraization or a canonical
PEL/contact-curve comparison. -/
theorem character_manifold :
    letI := characterTopologicalCharts i
    IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i) := by
  letI := characterTopologicalCharts i
  apply isManifold_of_contDiffOn
  rintro e f ⟨a,rfl⟩ ⟨b,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,
    Function.id_comp,Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ] using
    (transition_analyticOn i (chosenChart i a) (chosenChart i b)
      (chosenChart_original i a) (chosenChart_original i b)).contDiffOn
      ((chosenChart i a).symm.trans (chosenChart i b)).open_source.uniqueDiffOn

local instance : ChartedSpace ℂ (CharacterBase i) := characterTopologicalCharts i
local instance : IsManifold 𝓘(ℂ,ℂ) ω (CharacterBase i) := character_manifold i

/-- The original kernel quotient map is holomorphic at EVERY original
point, including every nontrivial stabilizer center. -/
theorem character_projection_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
    (toCharacter i) := by
  intro p
  let e := chosenChart i ((toCharacter i) p)
  have hp : (toCharacter i) p∈e.source := chosenChart_center i _
  have he : e∈IsManifold.maximalAtlas 𝓘(ℂ,ℂ) ω (CharacterBase i) :=
    IsManifold.subset_maximalAtlas ⟨(toCharacter i) p,rfl⟩
  have hL := lift_holomorphic i e (chosenChart_original i _) p hp
  have hI := contMDiffAt_symm_of_mem_maximalAtlas he (e.map_source hp)
  apply (hI.comp p hL).congr_of_eventuallyEq
  filter_upwards [(PELOriginalCharacterTopology318.toCharacter_continuous i).continuousAt.tendsto.eventually
    (e.open_source.mem_nhds hp)] with x hx
  exact (e.left_inv hx).symm

/-- The same upper-half-plane parameter reaches the character quotient by a
holomorphic map through the original norm-one base, without changing its
orbit relation or chosen topology. -/
theorem upper_projection_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω
    ((toCharacter i) ∘ PELUnlevelledComplexBase318.projection) := by
  exact (character_projection_holomorphic i).comp PELUnlevelledComplexBase318.projection_holomorphic
end PELOriginalCharacterComplexAtlas318
