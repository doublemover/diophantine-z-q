module
public import PELOriginalCharacterAllOpenInvariants318
public section
noncomputable section
namespace PELOriginalCharacterInvariantSections318
open AlgebraicGeometry CategoryTheory
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterPullback318
open PELOriginalCharacterAllOpenInvariants318

/-- Literal invariant regular sections on the full inverse image of
EVERY target open, including the unique empty-open section. -/
@[expose] def invariantSubring (i:Fin 4) (U:(Curve i).Opens):
    Subring Γ(Model,morphism i⁻¹ᵁU) where
  carrier:={x | Invariant i U x}
  zero_mem':=(range_iff i U 0).mp ⟨0,map_zero _⟩
  one_mem':=(range_iff i U 1).mp ⟨1,map_one _⟩
  add_mem':=by
    intro x y hx hy
    obtain ⟨a,ha⟩:=(range_iff i U x).mpr hx
    obtain ⟨b,hb⟩:=(range_iff i U y).mpr hy
    apply (range_iff i U (x+y)).mp
    exact ⟨a+b,by rw [map_add,ha,hb]⟩
  mul_mem':=by
    intro x y hx hy
    obtain ⟨a,ha⟩:=(range_iff i U x).mpr hx
    obtain ⟨b,hb⟩:=(range_iff i U y).mpr hy
    apply (range_iff i U (x*y)).mp
    exact ⟨a*b,by rw [map_mul,ha,hb]⟩
  neg_mem':=by
    intro x hx
    obtain ⟨a,ha⟩:=(range_iff i U x).mpr hx
    apply (range_iff i U (-x)).mp
    exact ⟨-a,by rw [map_neg,ha]⟩

@[expose] def toInvariant (i:Fin 4) (U:(Curve i).Opens):
    Γ(Curve i,U)→+*invariantSubring i U where
  toFun a:=⟨(morphism i).app U a,(range_iff i U _).mp ⟨a,rfl⟩⟩
  map_zero':=Subtype.ext (map_zero _)
  map_one':=Subtype.ext (map_one _)
  map_add' a b:=Subtype.ext (map_add _ a b)
  map_mul' a b:=Subtype.ext (map_mul _ a b)
lemma toInvariant_bijective (i:Fin 4) (U:(Curve i).Opens):
    Function.Bijective (toInvariant i U):=by
  constructor
  · intro a b h
    exact app_injective i U (congrArg Subtype.val h)
  · intro x
    obtain ⟨a,ha⟩:=(range_iff i U x.val).mpr x.property
    exact ⟨a,Subtype.ext ha⟩
@[expose] def sectionEquiv (i:Fin 4) (U:(Curve i).Opens):
    Γ(Curve i,U)≃+*invariantSubring i U:=
  RingEquiv.ofBijective (toInvariant i U) (toInvariant_bijective i U)
lemma sectionEquiv_val (i:Fin 4) (U:(Curve i).Opens) (a:Γ(Curve i,U)):
    (sectionEquiv i U a:Γ(Model,morphism i⁻¹ᵁU))=(morphism i).app U a:=rfl

@[expose] def restrict (i:Fin 4) {U V:(Curve i).Opens} (j:U⟶V):
    invariantSubring i V→+*invariantSubring i U where
  toFun x:=⟨Model.presheaf.map (homOfLE ((morphism i).preimage_mono j.le)).op x.val,
    invariant_restrict i j x.val x.property⟩
  map_zero':=Subtype.ext (map_zero _)
  map_one':=Subtype.ext (map_one _)
  map_add' x y:=Subtype.ext (map_add _ x.val y.val)
  map_mul' x y:=Subtype.ext (map_mul _ x.val y.val)

/-- The ring identifications commute with EVERY actual restriction.
This is an all-open statement, not merely agreement of global sections. -/
theorem restriction_square (i:Fin 4) {U V:(Curve i).Opens} (j:U⟶V)
    (a:Γ(Curve i,V)):
    restrict i j (sectionEquiv i V a)=
      sectionEquiv i U ((Curve i).presheaf.map j.op a):=by
  apply Subtype.ext
  exact (congrArg (fun k:Γ(Curve i,V)⟶Γ(Model,morphism i⁻¹ᵁU)=>k a)
    ((morphism i).naturality j.op)).symm
end PELOriginalCharacterInvariantSections318
