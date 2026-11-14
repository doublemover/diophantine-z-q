module
public import PELOriginalCompletedContactPoints318
public import FourRootGluedTopology318
public section
noncomputable section
namespace PELOriginalContactFiniteMapGerm318
open Set Filter
open scoped Topology OnePoint
open PELUnlevelledComplexBase318 PELOriginalContactRootFunctions318
open PELOriginalContactBranchSquare318 PELOriginalCommonContactBase318
open PELOriginalBranchLabels318 PELOriginalContactRootExtensions318
open PELOriginalContactParameterLocality318 PELOriginalCompletedContactPoints318
open FourRootNormalizedPointCharts318
local instance : TopologicalSpace (Completed branches):=FourRootGluedTopology318.topology branches
variable (p:UnlevelledBase) (hp:p∈nontrivialStabilizerLocus)
  (j:Fin 4) (h:normalizedMap p=(branches j:OnePoint ℂ))

lemma equations : ∀ᶠw in 𝓝 (0:ℂ),∀k,
    finiteRoots p hp j h k w^2=branches j+w^2-branches k := by
  obtain ⟨inv,hA,hG,hS,hj,hn,hd,hI,hI0,hL,hR,hE⟩:=
    (PELOriginalContactRootExtensions318.finite p hp j h).choose_spec
  filter_upwards [hE] with w hw
  intro k
  calc
    finiteRoots p hp j h k w^2=branches j-branches k+w^2:=hw k
    _=branches j+w^2-branches k:=by ring

/-- A total target-chart germ, agreeing with the actual analytic root
extensions on a whole neighborhood. Off that neighborhood its harmless
value is the SAME chosen center, not another branch point. -/
@[expose] def germ (w:ℂ):FinitePoints branches:=
  if hw:∀k,finiteRoots p hp j h k w^2=branches j+w^2-branches k then
    ⟨(branches j+w^2,fun k=>finiteRoots p hp j h k w),hw⟩
  else finiteCenter p hp j h

lemma value : (fun w=>(germ p hp j h w).val)=ᶠ[𝓝 (0:ℂ)]
    (fun w=>(branches j+w^2,fun k=>finiteRoots p hp j h k w)) := by
  filter_upwards [equations p hp j h] with w hw
  simp only [germ,dif_pos hw]
lemma center : germ p hp j h 0=finiteCenter p hp j h := by
  have hz:∀k,finiteRoots p hp j h k 0^2=branches j+(0:ℂ)^2-branches k:=by
    intro k
    simpa only [zero_pow (by decide:2≠0),add_zero] using finiteRoots_square p hp j h k
  apply Subtype.ext
  simp only [germ,dif_pos hz,zero_pow (by decide:2≠0),add_zero]
  rfl

lemma continuous : ContinuousAt (germ p hp j h) 0 := by
  have ht:ContinuousAt (fun w:ℂ=>branches j+w^2) 0:=by fun_prop
  have hz:ContinuousAt (fun w:ℂ k=>finiteRoots p hp j h k w) 0:=
    continuousAt_pi.mpr (fun k=>(finiteRoots_analytic p hp j h k).continuousAt)
  have hv:ContinuousAt (fun w=>(germ p hp j h w).val) 0:=
    (ht.prodMk hz).congr_of_eventuallyEq (value p hp j h)
  exact hv.subtype_mk _

/-- The fixed completed map, not a newly selected extension, agrees on
an ENTIRE parameter neighborhood with this independent target chart.
The center follows from its actual definition, all other nearby points
from full original regularity and simultaneous same-root equality. -/
theorem map_germ : (fun w=>completedMap (source (finiteParameter p hp j h) w))=ᶠ[𝓝 (0:ℂ)]
    (fun w=>finiteChart branches (germ p hp j h w)) := by
  have h0:=eventually_nhdsWithin_iff.mp (finiteRoots_agree p hp j h 0)
  have h1:=eventually_nhdsWithin_iff.mp (finiteRoots_agree p hp j h 1)
  have h2:=eventually_nhdsWithin_iff.mp (finiteRoots_agree p hp j h 2)
  have h3:=eventually_nhdsWithin_iff.mp (finiteRoots_agree p hp j h 3)
  have hr:=eventually_nhdsWithin_iff.mp
    (PELOriginalContactRootBranchSource318.finite_regular j (finiteParameter p hp j h))
  filter_upwards [h0,h1,h2,h3,hr,value p hp j h] with w h0w h1w h2w h3w hrw hv
  by_cases hw:w=0
  · subst w
    rw [source_zero,completedMap_finiteBranch p hp j h,center]
    rfl
  · have hh:=hrw hw
    rw [completedMap_regular _ hh.1]
    apply congrArg Sum.inl
    apply Subtype.ext
    rw [hv]
    apply Prod.ext hh.2
    funext k
    have hall:∀k,finiteRoots p hp j h k w=roots (source (finiteParameter p hp j h) w) k:=by
      intro k
      fin_cases k
      · exact h0w hw
      · exact h1w hw
      · exact h2w hw
      · exact h3w hw
    exact (hall k).symm

theorem along_source_continuous :
    ContinuousAt (fun w=>completedMap (source (finiteParameter p hp j h) w)) 0 :=
  ((FourRootGluedTopology318.finiteChart_continuous branches).continuousAt.comp
    (continuous p hp j h)).congr_of_eventuallyEq (map_germ p hp j h)
end PELOriginalContactFiniteMapGerm318
