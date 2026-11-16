module
public import PELMaximalComplexAtlas318
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Data.Set.Card
public section
noncomputable section
namespace PELMaximalQuotientProper318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318 PELOriginalChartLift318
open Set
set_option maxHeartbeats 1500000

/-- Every fiber of the literal maximal quotient is precisely its
original finite normalizer orbit, with no generic-fiber substitution. -/
theorem fiber_eq_orbit (p : UnlevelledBase) :
    {x : UnlevelledBase | PELOriginalMaximalQuotient318.projection x=
      PELOriginalMaximalQuotient318.projection p}=MulAction.orbit Labels p := by
  ext x
  exact (projection_eq_iff x p).trans MulAction.mem_orbit_iff.symm

theorem fiber_finite (q : MaximalBase) :
    {x : UnlevelledBase | PELOriginalMaximalQuotient318.projection x=q}.Finite := by
  obtain ⟨p,rfl⟩ := projection_surjective q
  rw [fiber_eq_orbit]
  have hr : MulAction.orbit Labels p=Set.range (fun g : Labels => g • p) := by
    ext x
    exact MulAction.mem_orbit_iff
  rw [hr]
  exact Set.finite_range _

/-- The original quotient is a closed map because saturation is a finite
union of inverse images under the actual continuous normalizer actions. -/
theorem projection_closed : IsClosedMap PELOriginalMaximalQuotient318.projection := by
  intro S hS
  have hq : IsQuotientMap PELOriginalMaximalQuotient318.projection :=
    isQuotientMap_quotient_mk'
  apply hq.isClosed_preimage.mp
  have he : PELOriginalMaximalQuotient318.projection ⁻¹'
      (PELOriginalMaximalQuotient318.projection '' S)=
      ⋃ g : Labels,(fun x : UnlevelledBase => g • x) ⁻¹' S := by
    ext x
    constructor
    · rintro ⟨y,hy,hqyx⟩
      obtain ⟨g,hg⟩ := (projection_eq_iff y x).mp hqyx
      exact Set.mem_iUnion.mpr ⟨g,by simpa only [hg] using hy⟩
    · intro hx
      obtain ⟨g,hg⟩ := Set.mem_iUnion.mp hx
      exact ⟨g • x,hg,projection_action g x⟩
  rw [he]
  exact isClosed_iUnion_of_finite (fun g => hS.preimage (continuous_const_smul g))

/-- Actual properness of the sixteen-element quotient MAP. This makes
no compactness assertion about either noncompact or compact base. -/
theorem projection_proper : IsProperMap PELOriginalMaximalQuotient318.projection := by
  apply isProperMap_iff_isClosedMap_and_compact_fibers.mpr
  refine ⟨projection_continuous,projection_closed,?_⟩
  intro q
  exact (fiber_finite q).isCompact
end PELMaximalQuotientProper318
