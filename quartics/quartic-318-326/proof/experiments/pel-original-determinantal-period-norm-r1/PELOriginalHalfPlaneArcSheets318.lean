module
public import PELOriginalAnalyticRealStrip318
public section
noncomputable section
namespace PELOriginalHalfPlaneArcSheets318
open Set
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalGlobalHalfPlaneSheets318 PELOriginalHalfPlaneDoubleCover318
open LegendreHalfPlaneAnalyticSheets318

abbrev Interior:=Ioo (0:ℝ) 1
local instance : SimplyConnectedSpace Interior:=by
  letI : ContractibleSpace Interior:=(convex_Ioo (0:ℝ) 1).contractibleSpace
    ⟨(1/2:ℝ),by constructor <;> norm_num⟩
  infer_instance
local instance : LocallyPathConnectedSpace Interior:=isOpen_Ioo.locallyPathConnectedSpace

/-- Any actual continuous original lift above an upper/lower base arc
uses ONE of the already fixed global sheets throughout the interior. No
new pointwise root or label choice can change along the arc. -/
theorem one_sheet (i:Fin 4) (upper:Bool) (base:ℝ→ℂ) (lift:ℝ→CharacterBase i)
    (hb:ContinuousOn base Interior) (hl:ContinuousOn lift Interior)
    (hs:∀t∈Interior,base t∈domain upper)
    (hp:∀t∈Interior,normalizedMap i (lift t)=(base t:OnePoint ℂ)) :
    ∃e:BaseFiber i upper,∀(t:ℝ)(ht:t∈Interior),sheet i upper e ⟨base t,hs t ht⟩=lift t := by
  let halfBase:C(Interior,Half upper):=
    ⟨fun t=>⟨base t.val,hs t.val t.property⟩,hb.continuous_restrict.subtype_mk _⟩
  let F:C(Interior,CharacterBase i):=⟨fun t=>lift t.val,hl.continuous_restrict⟩
  let G:C(Interior,OnePoint ℂ):=(baseMap upper).comp halfBase
  let t₀:Interior:=⟨(1/2:ℝ),by constructor <;> norm_num⟩
  obtain ⟨e,he,_⟩:=original_sheet_exhaustion i upper (halfBase t₀) (F t₀) (hp _ t₀.property)
  have hF:normalizedMap i ∘ F=G:=by funext t;exact hp _ t.property
  have hS:normalizedMap i ∘ (sheet i upper e).comp halfBase=G:=by
    funext t
    exact sheet_projection i upper e (halfBase t)
  have hu:=(covering_nonreal i).existsUnique_continuousMap_lifts G (hp _ t₀.property)
    (fun t=>baseMap_nonreal upper (halfBase t))
  have hh:(sheet i upper e).comp halfBase=F:=hu.unique ⟨he,hS⟩ ⟨rfl,hF⟩
  refine ⟨e,?_⟩
  intro t ht
  exact congrArg (fun f:C(Interior,CharacterBase i)=>f ⟨t,ht⟩) hh
end PELOriginalHalfPlaneArcSheets318
