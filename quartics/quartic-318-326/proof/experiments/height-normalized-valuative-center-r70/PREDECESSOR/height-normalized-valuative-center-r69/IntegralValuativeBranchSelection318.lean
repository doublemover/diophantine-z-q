module
public import IntegralValuativeGenericPoint318
public section
noncomputable section
namespace IntegralValuativeBranchSelection318
open Polynomial IntegralSourceBranches318 IntegralBranchDenominatorCover318 IsLocalRing
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (V : Type*) [CommRing V] [IsLocalRing V] (c : Fin 4 → Vˣ)
  (f : SourceOrder V c →+* V)

/-- The original full four-contact cover chooses a genuine branch chart for
any actual point over a local base. No noncontact avoidance is required. -/
theorem branch_exists (hN : IsUnit (separationInteger : V)) :
    ∃ i : Fin 4, IsUnit (f (denominator V c i)) := by
  by_contra! hn
  have hle : Ideal.span (Set.range (denominator V c)) ≤ (maximalIdeal V).comap f := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change f (denominator V c i)∈maximalIdeal V
    simpa only [mem_maximalIdeal,mem_nonunits_iff] using hn i
  rw [span_top V c hN] at hle
  have h1 : f 1∈maximalIdeal V := hle (show (1 : SourceOrder V c)∈(⊤ : Ideal (SourceOrder V c)) from trivial)
  rw [map_one] at h1
  exact (inferInstance : (maximalIdeal V).IsMaximal).ne_top (Ideal.eq_top_of_isUnit_mem _ h1 isUnit_one)

variable (i : Fin 4) (hi : IsUnit (f (denominator V c i)))
@[expose] def branchMap : IntegralBranchCoordinates318.B V c i →+* V :=
  IsLocalization.Away.lift (g := f) (denominator V c i) hi

theorem branchMap_source (a : SourceOrder V c) :
    branchMap V c f i hi (algebraMap (SourceOrder V c) (IntegralBranchCoordinates318.B V c i) a)=f a :=
  IsLocalization.Away.lift_eq _ hi a

theorem branchMap_root :
    branchMap V c f i hi (IntegralBranchCoordinates318.sourceCoordinate V c i)=
      f (IntegralOriginalRootCoordinates318.root V c i) := by
  rw [IntegralOriginalRootCoordinates318.coordinate_eq_root,branchMap_source]

theorem branchMap_parameter :
    branchMap V c f i hi (IntegralBranchCoordinates318.sourceT V c i)=
      f (algebraMap V[X] (SourceOrder V c) X) :=
  branchMap_source V c f i hi _
end IntegralValuativeBranchSelection318
