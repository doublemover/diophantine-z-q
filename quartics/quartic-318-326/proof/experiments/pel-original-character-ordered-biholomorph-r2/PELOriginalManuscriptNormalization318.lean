module
public import PELOriginalMarkedSphere318
public import PELOriginalFourBranchAlgebraicTarget318
public section
noncomputable section
namespace PELOriginalManuscriptNormalization318
open Set
open scoped OnePoint Manifold ContDiff
open PELOriginalMaximalQuotient318 PELMaximalTopologicalAtlas318 PELMaximalComplexAtlas318
open PELOriginalMarkedSphere318 ComplexSphereFourPointNormalization318
open ProjectiveLineComplexSchemePoints318 ProjectiveLineAlgebraicNormalization318
local instance : ChartedSpace ℂ MaximalBase:=maximalTopologicalCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω MaximalBase:=maximal_manifold
local instance : ChartedSpace ℂ (OnePoint ℂ):=ComplexSphereCharts318.sphereCharts
local instance : IsManifold 𝓘(ℂ,ℂ) ω (OnePoint ℂ):=ComplexSphereCharts318.sphere_manifold

/-- The PRESERVED MANUSCRIPT convention, not the earlier convenience
normalization: labels210,105,70,42 map to infinity,0,1,lambda. -/
@[expose] def orderedLabels : Fin 4→Fin 5:=![4,3,2,1]
lemma orderedLabels_injective : Function.Injective orderedLabels:=by decide
@[expose] def points (j:Fin 4) : OnePoint ℂ:=
  PELOriginalFourBranchCoordinate318.originalSphere (branchPoint (orderedLabels j))
lemma points_injective : Function.Injective points:=
  PELOriginalFourBranchCoordinate318.originalSphere.injective.comp
    (branchPoint_injective.comp orderedLabels_injective)
@[expose] def algebraic := ProjectiveLineFourPointAlgebraicNormalization318.fourPoints
  points points_injective
@[expose] def coordinate : MaximalBase≃ₜOnePoint ℂ:=
  PELOriginalFourBranchCoordinate318.originalSphere.trans (normalization points points_injective)
@[expose] def lambda : ℂ:=parameter points points_injective

lemma value210 : coordinate (branchPoint 4)=∞:=normalization_zero points points_injective
lemma value105 : coordinate (branchPoint 3)=(0:ℂ):=normalization_one points points_injective
lemma value70 : coordinate (branchPoint 2)=(1:ℂ):=normalization_two points points_injective
lemma value42 : coordinate (branchPoint 1)=(lambda:ℂ):=normalization_three points points_injective
lemma value30_finite : coordinate (branchPoint 0)≠∞:=by
  intro h
  have he:=branchPoint_injective (coordinate.injective (h.trans value210.symm))
  norm_num at he
@[expose] def mu : ℂ:=(OnePoint.ne_infty_iff_exists.mp value30_finite).choose
lemma value30 : coordinate (branchPoint 0)=(mu:ℂ):=
  (OnePoint.ne_infty_iff_exists.mp value30_finite).choose_spec.symm

lemma lambda_ne_zero : lambda≠0:=parameter_ne_zero points points_injective
lemma lambda_ne_one : lambda≠1:=parameter_ne_one points points_injective
lemma mu_ne_zero : mu≠0:=by
  intro h
  have he:=branchPoint_injective (coordinate.injective
    (value30.trans ((congrArg (fun z:ℂ=>(z:OnePoint ℂ)) h).trans value105.symm)))
  norm_num at he
lemma mu_ne_one : mu≠1:=by
  intro h
  have he:=branchPoint_injective (coordinate.injective
    (value30.trans ((congrArg (fun z:ℂ=>(z:OnePoint ℂ)) h).trans value70.symm)))
  norm_num at he
lemma lambda_ne_mu : lambda≠mu:=by
  intro h
  have he:=branchPoint_injective (coordinate.injective
    (value42.trans ((congrArg (fun z:ℂ=>(z:OnePoint ℂ)) h).trans value30.symm)))
  norm_num at he

lemma values : (fun j:Fin 5=>coordinate (branchPoint j))=
    ![(mu:ℂ),(lambda:ℂ),(1:ℂ),(0:ℂ),∞] := by
  funext j
  fin_cases j
  · exact value30
  · exact value42
  · exact value70
  · exact value105
  · exact value210

lemma biholomorphic : ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω coordinate ∧
    ContMDiff 𝓘(ℂ,ℂ) 𝓘(ℂ,ℂ) ω coordinate.symm:=by
  have hn:=normalization_biholomorphic points points_injective
  exact ⟨hn.1.comp PELOriginalFourBranchCoordinate318.originalSphere_holomorphic,
    PELOriginalFourBranchCoordinate318.originalSphere_inverse_holomorphic.comp hn.2⟩

/-- Same actual old Spec-C-valued point, postcomposed by the genuine
algebraic target automorphism implementing the manuscript convention. -/
@[expose] def schemePoint (q:MaximalBase) : SchemePoints:=
  pointMap algebraic.schemeIso.hom algebraic.over_base
    (PELOriginalFourBranchAlgebraicTarget318.originalPoint q)
lemma schemePoint_exact (q:MaximalBase) : schemePoint q=spherePoint (coordinate q):=by
  apply Subtype.ext
  exact algebraic.action (PELOriginalFourBranchCoordinate318.originalSphere q)

/-- Complete branch image with the correct original labels. No numerical
values are assigned until the actual quotient-invariant producers exist. -/
theorem branch_image : coordinate '' PELStabilizerLocusInvariant318.branchImage=
    ({∞,(0:ℂ),(1:ℂ),(lambda:ℂ),(mu:ℂ)}:Set (OnePoint ℂ)) := by
  rw [branchImage_eq_range,←range_comp]
  ext p
  constructor
  · rintro ⟨i,rfl⟩
    fin_cases i <;> simp only [Function.comp_apply] <;>
      simp [value30,value42,value70,value105,value210]
  · intro hp
    simp only [mem_insert_iff,mem_singleton_iff] at hp
    rcases hp with rfl|rfl|rfl|rfl|rfl
    · exact ⟨4,value210⟩
    · exact ⟨3,value105⟩
    · exact ⟨2,value70⟩
    · exact ⟨1,value42⟩
    · exact ⟨0,value30⟩
end PELOriginalManuscriptNormalization318
