module
public import PELOriginalCharacterAffineImage318
public section
noncomputable section
namespace PELOriginalCharacterInvariantRing318
open PELOriginalCommonContactBase318 PELOriginalActualCharacterFields318
open PELOriginalCharacterAffineImage318
open PELOriginalMaximalQuotient318 PELOriginalCharacterQuotient318 OriginalContactInertiaBasis318
local instance independentFact:Fact (QuadraticTower318.Independent
    (FourRootActualGenericField318.parameter branches)):=
  ⟨FourRootActualGenericField318.independent branches branches_injective⟩

/-- Actual regular functions on the whole original finite source whose
original field images lie in the exact character fixed field. -/
@[expose] def invariantSubring (i:Fin 4):Subring Source where
  carrier:={x | FourRootActualGenericField318.affineEmbedding branches x∈field i}
  zero_mem':=by simp
  one_mem':=by simp
  add_mem':=by
    intro x y hx hy
    simpa only [map_add] using add_mem hx hy
  mul_mem':=by
    intro x y hx hy
    simpa only [map_mul] using mul_mem hx hy
  neg_mem':=by
    intro x hx
    simpa only [map_neg] using neg_mem hx

@[expose] def toInvariant (i:Fin 4):Order i→+*invariantSubring i where
  toFun x:=⟨PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i x,
    (PELOriginalCharacterAffineImage318.range_iff i _).mp ⟨x,rfl⟩⟩
  map_zero':=Subtype.ext (map_zero _)
  map_one':=Subtype.ext (map_one _)
  map_add' x y:=Subtype.ext (map_add _ x y)
  map_mul' x y:=Subtype.ext (map_mul _ x y)

lemma toInvariant_injective (i:Fin 4):Function.Injective (toInvariant i):=by
  intro x y h
  exact PELOriginalOrderedCharacterSchemeMaps318.injective i (congrArg Subtype.val h)
lemma toInvariant_surjective (i:Fin 4):Function.Surjective (toInvariant i):=by
  intro x
  obtain ⟨y,hy⟩:=(PELOriginalCharacterAffineImage318.range_iff i x.val).mpr x.property
  exact ⟨y,Subtype.ext hy⟩

/-- The OLD ordered target ring is the actual whole affine invariant
ring. This is stronger than equality of fraction fields: every regular
fixed-field element is in the exact old target coordinate image. -/
@[expose] def coordinateEquiv (i:Fin 4):Order i≃+*invariantSubring i:=
  RingEquiv.ofBijective (toInvariant i) ⟨toInvariant_injective i,toInvariant_surjective i⟩
lemma coordinateEquiv_val (i:Fin 4) (x:Order i):
    (coordinateEquiv i x:Source)=PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i x:=rfl
lemma inclusion_square (i:Fin 4):(invariantSubring i).subtype.comp (coordinateEquiv i).toRingHom=
    (PELOriginalOrderedCharacterSchemeMaps318.mapOnRings i).toRingHom:=rfl

lemma member_fixed_field (i:Fin 4) (x:Source):x∈invariantSubring i ↔
    FourRootActualGenericField318.affineEmbedding branches x∈
      IntermediateField.fixedField (field i).fixingSubgroup:=by
  rw [PELOriginalActualCharacterFields318.actual_fixed_field]
  rfl
/-- This is literally a fixed subring, not only an abstract ring of the
same degree: the quantified automorphisms are the actual fixing subgroup. -/
lemma member_fixed_by_all (i:Fin 4) (x:Source):x∈invariantSubring i ↔
    ∀ σ∈(field i).fixingSubgroup,
      σ (FourRootActualGenericField318.affineEmbedding branches x)=
        FourRootActualGenericField318.affineEmbedding branches x:=by
  rw [member_fixed_field,IntermediateField.mem_fixedField_iff]

/-- All original analytic kernel labels fix these regular functions
under the independently defined whole affine root-sign action. -/
lemma fixed_by_original_kernel (i:Fin 4) (x:invariantSubring i)
    (g:Labels)
    (hg:g∈(character i).ker):
    FourRootCoordinateRingSigns318.finiteEnd branches
      (basis g) (x:Source)=(x:Source):=by
  apply FourRootActualGenericField318.affineEmbedding_injective branches
  rw [FourRootActualGenericSigns318.affineEmbedding_equivariant]
  exact (member_fixed_by_all i x.val).mp x.property _
    ((PELOriginalActualCharacterFields318.original_kernel i g).mpr hg)
end PELOriginalCharacterInvariantRing318
