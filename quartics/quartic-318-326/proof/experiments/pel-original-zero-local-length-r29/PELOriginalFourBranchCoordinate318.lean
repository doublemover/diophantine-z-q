module
public import ComplexSphereFourPointNormalization318
public import PELOriginalAnalyticSphere318
public import PELOriginalDirectCharacterBranches318
public section
noncomputable section
namespace PELOriginalFourBranchCoordinate318
open Set
open scoped OnePoint Manifold ContDiff
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELOriginalCharacterBranches318 PELOriginalDirectCharacterBranches318
open ComplexSphereCharts318 ComplexSphereFourPointNormalization318
local instance : ChartedSpace ℂ MaximalBase:=maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase:=maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=sphere_manifold

/-- The actual sphere comparison is supplied by the completed original
arithmetic construction, not an input to this branch-coordinate producer. -/
@[expose] def originalSphere : MaximalBase≃ₜOnePoint ℂ:=
  PELOriginalAnalyticSphere318.original_analytic_sphere.choose
lemma originalSphere_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω originalSphere:=
  PELOriginalAnalyticSphere318.original_analytic_sphere.choose_spec.1
lemma originalSphere_inverse_holomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω originalSphere.symm:=
  PELOriginalAnalyticSphere318.original_analytic_sphere.choose_spec.2.1

@[expose] def visibleEnumeration (i:Fin 4) : Fin 4≃
    {j:Fin 5 // InertiaLabels318.fiveLabels j i≠0}:=
  (Fintype.equivFinOfCardEq (visible_labels_card i)).symm
@[expose] def actualBranches (i:Fin 4) : Fin 4≃CharacterBranchValues i:=
  (visibleEnumeration i).trans (PELOriginalDirectCharacterBranches318.branchEnumeration i)
@[expose] def sphereBranches (i:Fin 4) (j:Fin 4) : OnePoint ℂ:=
  originalSphere (actualBranches i j).val
lemma sphereBranches_injective (i:Fin 4) : Function.Injective (sphereBranches i):=by
  intro j k he
  apply (actualBranches i).injective
  apply Subtype.ext
  exact originalSphere.injective he

/-- Genuine analytic coordinate on the ORIGINAL maximal quotient,
normalized at three actual branch values of the actual character map. -/
@[expose] def coordinate (i:Fin 4) : MaximalBase≃ₜOnePoint ℂ:=
  originalSphere.trans (normalization (sphereBranches i) (sphereBranches_injective i))
@[expose] def branchParameter (i:Fin 4) : ℂ:=
  parameter (sphereBranches i) (sphereBranches_injective i)

lemma branchParameter_nonexceptional (i:Fin 4) : branchParameter i≠0 ∧ branchParameter i≠1:=
  ⟨parameter_ne_zero _ _,parameter_ne_one _ _⟩
lemma coordinate_biholomorphic (i:Fin 4) :
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (coordinate i) ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω (coordinate i).symm:=by
  have hh:=normalization_biholomorphic (sphereBranches i) (sphereBranches_injective i)
  exact ⟨hh.1.comp originalSphere_holomorphic,originalSphere_inverse_holomorphic.comp hh.2⟩

/-- All four values retain the actual old branch subtype and ordering.
No arithmetic value for the fourth cross-ratio is guessed or assumed. -/
lemma original_values (i:Fin 4) :
    (fun j:Fin 4=>coordinate i (actualBranches i j).val)=
      ![∞,(0:ℂ),(1:ℂ),(branchParameter i:ℂ)] := by
  funext j
  fin_cases j
  · exact normalization_zero _ _
  · exact normalization_one _ _
  · exact normalization_two _ _
  · exact normalization_three _ _

/-- Exhaustion of the ACTUAL cardinality-defined branch values after
normalization, not merely four points asserted to be branch values. -/
theorem actual_branch_values (i:Fin 4) (q:MaximalBase) :
    q∈CharacterBranchValues i ↔
      coordinate i q=∞ ∨ coordinate i q=(0:ℂ) ∨
      coordinate i q=(1:ℂ) ∨ coordinate i q=(branchParameter i:ℂ) := by
  have hv:=original_values i
  constructor
  · intro hq
    obtain ⟨j,hj⟩:=(actualBranches i).surjective ⟨q,hq⟩
    have he:=congrArg (fun r:CharacterBranchValues i=>coordinate i r.val) hj
    have hh:=congrFun hv j
    rw [he] at hh
    fin_cases j <;> simp_all
  · intro hq
    have hex:∃j:Fin 4,coordinate i q=coordinate i (actualBranches i j).val:=by
      rcases hq with h|h|h|h
      · exact ⟨0,h.trans (congrFun hv 0).symm⟩
      · exact ⟨1,h.trans (congrFun hv 1).symm⟩
      · exact ⟨2,h.trans (congrFun hv 2).symm⟩
      · exact ⟨3,h.trans (congrFun hv 3).symm⟩
    obtain ⟨j,hj⟩:=hex
    rw [(coordinate i).injective hj]
    exact (actualBranches i j).property
end PELOriginalFourBranchCoordinate318
