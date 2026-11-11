module
public import PELOriginalCompletedContactBiholomorph318
public import PELOriginalContactRootDeck318
public import FourRootNormalizedSignAction318
public section
noncomputable section
namespace PELOriginalCompletedContactDeck318
open Set
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalContactRootFunctions318 PELOriginalCommonContactBase318
open PELOriginalCompletedContactPoints318 PELOriginalContactRootDeck318
open FourRootNormalizedPointCharts318 OriginalContactInertiaBasis318
local instance : TopologicalSpace (Completed branches):=FourRootGluedTopology318.topology branches
local instance : T2Space (Completed branches):=FourRootCompletedHausdorff318.hausdorff branches

lemma generic_equivariant (g:Labels) (x:UnlevelledBase) (hx:x∈RegularSource):
    completedMap (g • x)=FourRootNormalizedSignAction318.action branches (basis g) (completedMap x):=by
  rw [completedMap_regular _ (original_regular g x hx),completedMap_regular x hx]
  apply congrArg Sum.inl
  apply Subtype.ext
  apply Prod.ext (base_action g x)
  funext i
  exact roots_action g x hx i

/-- The full ORIGINAL deck action intertwines the explicit normalized
root action on EVERY point, including all finite ramification points and
all eight infinity signs. Extension is forced by actual continuity and
the original dense regular locus, not independently assigned at branches. -/
theorem equivariant (g:Labels) (x:UnlevelledBase):
    completedMap (g • x)=FourRootNormalizedSignAction318.action branches (basis g) (completedMap x):=by
  have hleft:Continuous (fun p:UnlevelledBase=>completedMap (g • p)):=
    PELOriginalCompletedContactContinuity318.continuous.comp (continuous_const_smul g)
  have hright:Continuous (fun p:UnlevelledBase=>
      FourRootNormalizedSignAction318.action branches (basis g) (completedMap p)):=
    (FourRootNormalizedSignAction318.continuous branches (basis g)).comp
      PELOriginalCompletedContactContinuity318.continuous
  have hc:IsClosed {p:UnlevelledBase|completedMap (g • p)=
      FourRootNormalizedSignAction318.action branches (basis g) (completedMap p)}:=
    isClosed_eq hleft hright
  exact closure_minimal (fun p hp=>generic_equivariant g p hp) hc
    (PELOriginalContactRegularDensity318.regular_dense x)

lemma actual_comparison_equivariant (g:Labels) (x:UnlevelledBase):
    PELOriginalCompletedContactBiholomorph318.comparison (g • x)=
      FourRootNormalizedSignAction318.homeomorph branches (basis g)
        (PELOriginalCompletedContactBiholomorph318.comparison x):=
  equivariant g x
end PELOriginalCompletedContactDeck318
