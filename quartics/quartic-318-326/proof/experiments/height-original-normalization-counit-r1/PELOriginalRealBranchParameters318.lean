module
public import PELOriginalBranchCutRepresentatives318
public import ComplexSphereImaginaryNormalization318
public import PELOriginalFourBranchCoordinate318
public section
noncomputable section
namespace PELOriginalRealBranchParameters318
open Set
open scoped OnePoint
open PELOriginalMaximalQuotient318 PELOriginalFourBranchCoordinate318
open PELOriginalConformalComparisonInputs318 PELOriginalOpenDenseInterior318
open PELMaximalHalfOctagonOriginalPoints318 ComplexSphereRegularTarget318
open PELOriginalBranchCutRepresentatives318 ComplexSphereImaginaryNormalization318
open PELStabilizerLocusInvariant318 PELOriginalMarkedSphere318

/-- The chosen existing sphere producer sends EVERY actual branch value to
its seam axis. This uses actual cut representatives plus injectivity, not
an assumed extension formula or a topological/Klein coordinate. -/
theorem originalSphere_branch_not_regular (q:MaximalBase) (hq:q∈branchImage) :
    originalSphere q∉regular := by
  intro hr
  obtain ⟨e,hs,ht,ha⟩:=PELOriginalAnalyticSphere318.original_analytic_sphere.choose_spec.2.2
  obtain ⟨z,hz,hzp⟩:=actual_interior_cover e hs ht (originalSphere q) hr
  have he:originalSphere (maximalProjection ⟨z,hz.1⟩)=originalSphere q := by
    rw [ha ⟨z,hz.1⟩ hz]
    exact hzp
  have hqeq:=originalSphere.injective he
  exact branch_not_interior q hq (hqeq ▸ (show maximalProjection ⟨z,hz.1⟩∈originalInterior from
    ⟨⟨z,hz.1⟩,hz,rfl⟩))

theorem originalSphere_branch_axis (q:MaximalBase) (hq:q∈branchImage) :
    OnAxis (originalSphere q) := by
  by_cases hi:originalSphere q=∞
  · exact Or.inl hi
  · obtain ⟨z,hz⟩:=OnePoint.ne_infty_iff_exists.mp hi
    refine Or.inr ⟨z,?_,hz⟩
    by_contra h
    exact originalSphere_branch_not_regular q hq ⟨z,h,hz⟩

theorem sphereBranches_axis (i:Fin 4) (j:Fin 4) : OnAxis (sphereBranches i j) := by
  apply originalSphere_branch_axis
  obtain ⟨k,_,hk⟩:=
    (PELOriginalDirectCharacterBranches318.branch_values_iff i (actualBranches i j).val).mp
      (actualBranches i j).property
  rw [hk,branchImage_eq_range]
  exact ⟨k,rfl⟩

/-- The exact parameter already consumed by the concrete Legendre scheme
is real. It is not a new chosen parameter and no rational value is inferred. -/
theorem branchParameter_im_zero (i:Fin 4) : (branchParameter i).im=0 :=
  parameter_im_zero (sphereBranches i) (sphereBranches_injective i) (sphereBranches_axis i)

theorem branchParameter_eq_real (i:Fin 4) :
    branchParameter i=((branchParameter i).re:ℂ) := by
  apply Complex.ext
  · simp
  · simp [branchParameter_im_zero]

theorem realParameter_nonexceptional (i:Fin 4) :
    (branchParameter i).re≠0 ∧ (branchParameter i).re≠1 := by
  constructor
  · intro h
    apply (branchParameter_nonexceptional i).1
    rw [branchParameter_eq_real,h]
    norm_num
  · intro h
    apply (branchParameter_nonexceptional i).2
    rw [branchParameter_eq_real,h]
    norm_num
end PELOriginalRealBranchParameters318
