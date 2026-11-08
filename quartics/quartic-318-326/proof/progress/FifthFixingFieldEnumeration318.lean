module
public import FifthFixingSigns318
public import FifthGenericTrace318
public section
noncomputable section
namespace FifthFixingFieldEnumeration318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open scoped BigOperators
set_option maxHeartbeats 450000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
abbrev H:=FifthCharacterField318.field.fixingSubgroup
abbrev B:={b:Fin 4→Bool //b∈FifthFixingSigns318.signs}
local instance rawField:Field FifthCharacterField318.L:=(KummerTensorField318.source_raw_field units).toField
local instance finiteH:Finite H:=by
  apply Nat.finite_of_card_ne_zero
  rw [FifthCharacterField318.fixing_subgroup_card]
  decide
local instance fintypeH:Fintype H:=Fintype.ofFinite _
lemma sign_mem (b:Fin 4→Bool):
    FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b∈
      FifthCharacterField318.field.fixingSubgroup ↔ b∈FifthFixingSigns318.signs:=by
  rw [FifthCharacterField318.sign_mem_fixing_iff]
  change FifthSignAffine318.sign b=1 ↔ _
  rw [FifthFixingSigns318.sign_matches]
  simp only [FifthFixingSigns318.signs,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro h
    apply (algebraMap ℚ (RatFunc ℚ)).injective
    simpa only [map_one] using h
  · intro h;rw [h,map_one]
/-- Enumeration by the exact Boolean maps, not an arbitrary bijection of
sets of cardinal eight. -/
@[expose] def toFixing (b:B):H:=
  ⟨FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b.val,
    (sign_mem b.val).mpr b.property⟩
lemma injective:Function.Injective toFixing:=by
  intro b c h
  apply Subtype.ext
  apply FourRootAutomorphisms318.signEquiv_injective (SourceKummerField318.parameter units)
  exact congrArg Subtype.val h
lemma bijective:Function.Bijective toFixing:=by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨injective,?_⟩
  calc
    Fintype.card B=8:=by simpa only [Fintype.card_coe] using FifthFixingSigns318.cardinality
    _=Fintype.card H:=by simpa only [Nat.card_eq_fintype_card] using FifthCharacterField318.fixing_subgroup_card.symm
@[expose] def equiv:B≃H:=Equiv.ofBijective toFixing bijective
/-- The sign-indexed sum equals the sum of every genuine fixing field
automorphism, with precisely its original action on the original field. -/
theorem sum_eq (x:FifthCharacterField318.L):
    (∑b∈FifthFixingSigns318.signs,
      FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units) b x)=
    ∑σ:H,σ.1 x:=by
  rw [←Finset.sum_coe_sort]
  exact Fintype.sum_equiv equiv _ _ (fun _=>rfl)
end FifthFixingFieldEnumeration318
