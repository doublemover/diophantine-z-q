module
public import SimplyConnectedCoverSheets318
public import PELOriginalHalfPlaneDoubleCover318
public import LegendreHalfPlaneAnalyticSheets318
public section
noncomputable section
namespace PELOriginalGlobalHalfPlaneSheets318
open Set
open scoped OnePoint
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318
open PELOriginalHalfPlaneDoubleCover318 LegendreHalfPlaneAnalyticSheets318

abbrev Half (upper:Bool):=domain upper
local instance (upper:Bool) : SimplyConnectedSpace (Half upper):=domain_simplyConnected upper
local instance (upper:Bool) : LocallyPathConnectedSpace (Half upper):=
  (domain_open upper).locallyPathConnectedSpace

@[expose] def basepoint (upper:Bool) : Half upper :=
  ⟨if upper then Complex.I else -Complex.I,by cases upper <;> norm_num [domain,side]⟩
@[expose] def baseMap (upper:Bool) : C(Half upper,OnePoint ℂ):=
  ⟨fun z=>(z.val:OnePoint ℂ),OnePoint.continuous_coe.comp continuous_subtype_val⟩
lemma baseMap_nonreal (upper:Bool) (z:Half upper) : baseMap upper z∈nonreal :=
  ⟨z.val,domain_nonreal upper z.val z.property,rfl⟩

/-- A fixed COMPLETE actual original fiber, not independently chosen signs. -/
abbrev BaseFiber (i:Fin 4) (upper:Bool):=
  SimplyConnectedCoverSheets318.Fiber (normalizedMap i) (baseMap upper) (basepoint upper)

/-- Globally continuous original sheets, constructed by lifting through the
proved original covering. Their index remains the actual two-point base fiber. -/
@[expose] def sheet (i:Fin 4) (upper:Bool) (e:BaseFiber i upper) : C(Half upper,CharacterBase i):=
  SimplyConnectedCoverSheets318.sheet (normalizedMap i) nonreal (covering_nonreal i)
    (baseMap upper) (baseMap_nonreal upper) (basepoint upper) e

lemma sheet_projection (i:Fin 4) (upper:Bool) (e:BaseFiber i upper) (z:Half upper) :
    normalizedMap i (sheet i upper e z)=(z.val:OnePoint ℂ) :=
  congrFun (SimplyConnectedCoverSheets318.sheet_lifts (normalizedMap i) nonreal (covering_nonreal i)
    (baseMap upper) (baseMap_nonreal upper) (basepoint upper) e) z
lemma sheet_basepoint (i:Fin 4) (upper:Bool) (e:BaseFiber i upper) :
    sheet i upper e (basepoint upper)=e.val :=
  SimplyConnectedCoverSheets318.sheet_base (normalizedMap i) nonreal (covering_nonreal i)
    (baseMap upper) (baseMap_nonreal upper) (basepoint upper) e

theorem baseFiber_card_two (i:Fin 4) (upper:Bool) : Nat.card (BaseFiber i upper)=2 := by
  change Nat.card {x:CharacterBase i // normalizedMap i x=((basepoint upper).val:OnePoint ℂ)}=2
  rw [all_fibers]
  exact if_neg (nonreal_avoids_branches i (basepoint upper).val
    (domain_nonreal upper _ (basepoint upper).property))

/-- The TWO continuous global sheets remain distinct at every base point. -/
theorem sheets_never_meet (i:Fin 4) (upper:Bool) (z:Half upper) :
    Function.Injective (fun e:BaseFiber i upper=>sheet i upper e z) :=
  SimplyConnectedCoverSheets318.sheet_injective_at (normalizedMap i) nonreal (covering_nonreal i)
    (baseMap upper) (baseMap_nonreal upper) (basepoint upper) z

/-- Every actual original point above the entire half-plane lies on one
and only one global continuous sheet. No connectedness of the TOTAL source
has been assumed; it is precisely two distinct sheets here. -/
theorem original_sheet_exhaustion (i:Fin 4) (upper:Bool) (z:Half upper) (x:CharacterBase i)
    (hx:normalizedMap i x=(z.val:OnePoint ℂ)) :
    ∃!e:BaseFiber i upper,sheet i upper e z=x := by
  obtain ⟨e,he⟩:=SimplyConnectedCoverSheets318.sheet_exhaustive (normalizedMap i) nonreal
    (covering_nonreal i) (baseMap upper) (baseMap_nonreal upper) (basepoint upper) z x hx
  exact ⟨e,he,fun d hd=>(sheets_never_meet i upper z) (hd.trans he.symm)⟩

/-- Whole actual point-fiber equivalence varies through the constructed
continuous sheets, not arbitrary pointwise choices. Analytic upgrade and
compatibility across the real cuts remain separate obligations. -/
@[expose] def originalFiberEquiv (i:Fin 4) (upper:Bool) (z:Half upper) :
    BaseFiber i upper≃{x:CharacterBase i // normalizedMap i x=(z.val:OnePoint ℂ)} :=
  SimplyConnectedCoverSheets318.fiberEquiv (normalizedMap i) nonreal (covering_nonreal i)
    (baseMap upper) (baseMap_nonreal upper) (basepoint upper) z
end PELOriginalGlobalHalfPlaneSheets318
