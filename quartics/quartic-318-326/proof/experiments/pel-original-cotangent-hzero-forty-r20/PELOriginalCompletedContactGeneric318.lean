module
public import PELOriginalCompletedContactPoints318
public section
noncomputable section
namespace PELOriginalCompletedContactGeneric318
open Set
open scoped OnePoint
open PELUnlevelledComplexBase318 PELOriginalContactRootFunctions318
open PELOriginalContactBranchSquare318 PELOriginalCommonContactBase318
open PELOriginalCompletedContactPoints318 FourRootNormalizedPointCharts318
open FourCharacterRootRecombination318

/-- The actual generic finite region of the independent normalized root
model: remove precisely the four finite branch values and infinity. -/
@[expose] def Generic : Set (Completed branches):=
  {p|∃q:FinitePoints branches,p=.inl q ∧ denominator branches q.val.1≠0}

lemma regular_maps_generic (x:UnlevelledBase) (hx:x∈RegularSource):
    completedMap x∈Generic:=
  ⟨⟨(base x,roots x),roots_square x hx⟩,completedMap_regular x hx,denominator_ne x hx⟩

/-- ALL preimages of the generic target are in the genuine original
regular locus. Exceptional source points cannot silently enter generic
fibers and defeat the uniqueness theorem. -/
lemma generic_preimage (x:UnlevelledBase) (hx:completedMap x∈Generic):
    x∈RegularSource := by
  obtain ⟨q,hq,hD⟩:=hx
  have hp:normalizedMap x=(q.val.1:OnePoint ℂ):=by
    rw [←projection_commutes x,hq]
    rfl
  exact (PELOriginalContactRootBranchSource318.regular_of_projection x q.val.1 hp hD).1

lemma generic_preimage_iff (x:UnlevelledBase):completedMap x∈Generic ↔ x∈RegularSource:=
  ⟨generic_preimage x,regular_maps_generic x⟩

theorem generic_fiber_unique (x y:UnlevelledBase)
    (hxy:completedMap x=completedMap y) (hx:completedMap x∈Generic) : x=y := by
  have hxr:=generic_preimage x hx
  have hyr:=generic_preimage y (hxy ▸ hx)
  rw [completedMap_regular x hxr,completedMap_regular y hyr] at hxy
  have he:(base x,roots x)=(base y,roots y):=congrArg Subtype.val (Sum.inl.inj hxy)
  exact base_roots_injective x y hxr hyr (congrArg Prod.fst he)
    (fun k=>congrArg (fun v:ℂ×(Fin 4→ℂ)=>v.2 k) he)

/-- Every actual generic target point is realized by the fixed completed
map. This uses the full original sixteen-fiber construction, not a
cardinality match or a chosen component of the source. -/
theorem generic_covered : Generic⊆range completedMap := by
  rintro q ⟨p,rfl,hD⟩
  obtain ⟨x,hx,ht,hz⟩:=all_roots p.val.1 hD p.val.2 p.property
  refine ⟨x,?_⟩
  rw [completedMap_regular x hx]
  congr 1
  apply Subtype.ext
  exact Prod.ext ht (funext hz)
end PELOriginalCompletedContactGeneric318
