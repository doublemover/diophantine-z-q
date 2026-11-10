module
public import PELDescendedInertiaChart318
public section
noncomputable section
namespace PELStabilizerLocusInvariant318
open PELOriginalMaximalQuotient318 PELUnlevelledComplexBase318 PELOriginalBranchLabels318
open PELOriginalElementaryAction318
set_option maxHeartbeats 1200000

theorem action_commute (g h : Labels) (x : UnlevelledBase) :
    g • (h • x)=h • (g • x) := by rw [←mul_smul,mul_comm,mul_smul]

theorem stabilizer_locus_invariant (g : Labels) (x : UnlevelledBase) :
    g • x∈nontrivialStabilizerLocus ↔ x∈nontrivialStabilizerLocus := by
  constructor
  · rintro ⟨v,hv,hfix⟩
    refine ⟨v,hv,?_⟩
    rw [action_commute] at hfix
    have h := congrArg (fun y => g⁻¹ • y) hfix
    simpa only [inv_smul_smul] using h
  · rintro ⟨v,hv,hfix⟩
    refine ⟨v,hv,?_⟩
    rw [action_commute,hfix]

@[expose] def branchImage : Set MaximalBase :=
  PELOriginalMaximalQuotient318.projection '' nontrivialStabilizerLocus

theorem branch_image_iff (x : UnlevelledBase) :
    PELOriginalMaximalQuotient318.projection x∈branchImage ↔ x∈nontrivialStabilizerLocus := by
  constructor
  · rintro ⟨y,hy,hq⟩
    obtain ⟨g,hg⟩ := (PELOriginalMaximalQuotient318.projection_eq_iff y x).mp hq
    rw [←hg] at hy
    exact (stabilizer_locus_invariant g x).mp hy
  · intro hx
    exact ⟨x,hx,rfl⟩
end PELStabilizerLocusInvariant318
