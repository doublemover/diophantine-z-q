module
public import PELStabilizerLocusIsolation318
public section
noncomputable section
namespace PELQuotientBranchIsolation318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318 PELOriginalBranchLabels318
open PELStabilizerLocusInvariant318 PELStabilizerLocusIsolation318 Filter Topology
set_option maxHeartbeats 1700000

/-- An actual open neighborhood downstairs contains no branching whenever
the original full normalizer stabilizer is trivial. -/
theorem regular_image_neighborhood (q : MaximalBase) (hq : q∉branchImage) :
    ∃ W : Set MaximalBase,IsOpen W ∧ q∈W ∧ ∀ z∈W,z∉branchImage := by
  obtain ⟨p,rfl⟩ := PELOriginalMaximalQuotient318.projection_surjective q
  have hp : p∉nontrivialStabilizerLocus := by
    intro h
    exact hq ((branch_image_iff p).mpr h)
  obtain ⟨U,hU,hpU,hfree⟩ := regular_neighborhood p hp
  refine ⟨PELOriginalMaximalQuotient318.projection '' U,
    PELOriginalMaximalQuotient318.projection_open U hU,⟨p,hpU,rfl⟩,?_⟩
  rintro z ⟨y,hy,rfl⟩ hz
  exact hfree y hy ((branch_image_iff y).mp hz)

/-- The actual branch image in the literal full quotient is locally a
SINGLE point at every branch point. This proves isolation, not a global
five-point count or compactness. -/
theorem branch_image_neighborhood (q : MaximalBase) (hq : q∈branchImage) :
    ∃ W : Set MaximalBase,IsOpen W ∧ q∈W ∧ ∀ z∈W,z∈branchImage ↔ z=q := by
  obtain ⟨p,hp,rfl⟩ := hq
  obtain ⟨U,hU,hpU,hiso⟩ := branch_neighborhood p hp
  refine ⟨PELOriginalMaximalQuotient318.projection '' U,
    PELOriginalMaximalQuotient318.projection_open U hU,⟨p,hpU,rfl⟩,?_⟩
  rintro z ⟨y,hy,rfl⟩
  constructor
  · intro hz
    have he := (hiso y hy).mp ((branch_image_iff y).mp hz)
    exact congrArg PELOriginalMaximalQuotient318.projection he
  · intro he
    rw [he]
    exact (branch_image_iff p).mpr hp

theorem branch_image_closed : IsClosed branchImage := by
  have hc : IsOpen branchImageᶜ := by
    apply isOpen_iff_mem_nhds.mpr
    intro q hq
    obtain ⟨W,hW,hqW,hfree⟩ := regular_image_neighborhood q hq
    exact Filter.mem_of_superset (hW.mem_nhds hqW) (fun z hz => hfree z hz)
  exact isOpen_compl_iff.mp hc
end PELQuotientBranchIsolation318
