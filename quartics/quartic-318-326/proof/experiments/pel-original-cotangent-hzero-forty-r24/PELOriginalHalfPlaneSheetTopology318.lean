module
public import PELOriginalOpenHalfPlaneSheets318
public import PELOriginalAnalyticHalfPlaneSheets318
public import Mathlib.Data.Fintype.EquivFin
public section
noncomputable section
namespace PELOriginalHalfPlaneSheetTopology318
open Set Topology
open scoped OnePoint
open PELOriginalGlobalHalfPlaneSheets318 LegendreHalfPlaneAnalyticSheets318
open PELOriginalCharacterQuotient318 PELOriginalNormalizedDoubleCover318

/-- The WHOLE original inverse halfplane with its unchanged subspace topology. -/
abbrev Total (i:Fin 4) (upper:Bool):=
  {x:CharacterBase i // normalizedMap i x∈((↑):ℂ→OnePoint ℂ) '' domain upper}

/-- A single choice of labels for the complete actual base fiber. This choice
is made once per connected halfplane, NOT independently at each point.
Matching the choices across the real cuts is deliberately not asserted. -/
@[expose] def enumeration (i:Fin 4) (upper:Bool) : Bool≃BaseFiber i upper := by
  letI : Finite (BaseFiber i upper):=Nat.finite_of_card_ne_zero (by rw [baseFiber_card_two]; norm_num)
  letI : Fintype (BaseFiber i upper):=Fintype.ofFinite _
  apply Fintype.equivOfCardEq
  calc
    Fintype.card Bool=2:=by decide
    _=Fintype.card (BaseFiber i upper):=by rw [←Nat.card_eq_fintype_card,baseFiber_card_two]

@[expose] def sheet (i:Fin 4) (upper:Bool) (positive:Bool) (z:Half upper) : Total i upper:=
  ⟨PELOriginalGlobalHalfPlaneSheets318.sheet i upper (enumeration i upper positive) z,
    ⟨z.val,z.property,(sheet_projection i upper (enumeration i upper positive) z).symm⟩⟩

lemma sheet_projection (i:Fin 4) (upper:Bool) (positive:Bool) (z:Half upper) :
    normalizedMap i (sheet i upper positive z).val=(z.val:OnePoint ℂ):=
  PELOriginalGlobalHalfPlaneSheets318.sheet_projection i upper (enumeration i upper positive) z
lemma sheet_continuous (i:Fin 4) (upper:Bool) (positive:Bool) : Continuous (sheet i upper positive):=
  (PELOriginalGlobalHalfPlaneSheets318.sheet i upper (enumeration i upper positive)).continuous.subtype_mk _
lemma sheet_open (i:Fin 4) (upper:Bool) (positive:Bool) : IsOpenMap (sheet i upper positive):=
  (PELOriginalOpenHalfPlaneSheets318.sheet_openEmbedding i upper
    (enumeration i upper positive)).isOpenMap.subtype_mk _
lemma sheet_injective (i:Fin 4) (upper:Bool) (positive:Bool) :
    Function.Injective (sheet i upper positive) := by
  intro z w h
  have hp:=congrArg (fun x:Total i upper=>normalizedMap i x.val) h
  rw [sheet_projection,sheet_projection] at hp
  exact Subtype.ext (OnePoint.coe_injective hp)
lemma sheet_openEmbedding (i:Fin 4) (upper:Bool) (positive:Bool) :
    IsOpenEmbedding (sheet i upper positive):=
  isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
    ⟨sheet_continuous i upper positive,sheet_injective i upper positive,sheet_open i upper positive⟩

lemma sheet_label_injective (i:Fin 4) (upper:Bool) (z:Half upper) :
    Function.Injective (fun positive=>sheet i upper positive z) := by
  intro a b h
  apply (enumeration i upper).injective
  apply sheets_never_meet i upper z
  exact congrArg Subtype.val h

lemma all_sheets (i:Fin 4) (upper:Bool) (x:Total i upper) :
    ∃z:Half upper, x=sheet i upper true z ∨ x=sheet i upper false z := by
  rcases x.property with ⟨z,hz,hx⟩
  obtain ⟨e,he,_⟩:=original_sheet_exhaustion i upper ⟨z,hz⟩ x.val hx.symm
  obtain ⟨b,hb⟩:=(enumeration i upper).surjective e
  subst e
  refine ⟨⟨z,hz⟩,?_⟩
  cases b
  · exact Or.inr (Subtype.ext he.symm)
  · exact Or.inl (Subtype.ext he.symm)

@[expose] def fromSum (i:Fin 4) (upper:Bool) : Half upper⊕Half upper→Total i upper:=
  Sum.elim (sheet i upper true) (sheet i upper false)
lemma fromSum_continuous (i:Fin 4) (upper:Bool) : Continuous (fromSum i upper):=
  continuous_sum_dom.mpr ⟨sheet_continuous i upper true,sheet_continuous i upper false⟩
lemma fromSum_bijective (i:Fin 4) (upper:Bool) : Function.Bijective (fromSum i upper) := by
  constructor
  · intro z w h
    cases z with
    | inl z=>
      cases w with
      | inl w=>exact congrArg Sum.inl (sheet_injective i upper true h)
      | inr w=>
        have hp:=congrArg (fun x:Total i upper=>normalizedMap i x.val) h
        change normalizedMap i (sheet i upper true z).val=normalizedMap i (sheet i upper false w).val at hp
        rw [sheet_projection,sheet_projection] at hp
        have hz:z=w:=Subtype.ext (OnePoint.coe_injective hp)
        subst w
        have hb: true=false:=sheet_label_injective i upper z h
        cases hb
    | inr z=>
      cases w with
      | inl w=>
        have hp:=congrArg (fun x:Total i upper=>normalizedMap i x.val) h
        change normalizedMap i (sheet i upper false z).val=normalizedMap i (sheet i upper true w).val at hp
        rw [sheet_projection,sheet_projection] at hp
        have hz:z=w:=Subtype.ext (OnePoint.coe_injective hp)
        subst w
        have hb: false=true:=sheet_label_injective i upper z h
        cases hb
      | inr w=>exact congrArg Sum.inr (sheet_injective i upper false h)
  · intro x
    obtain ⟨z,hz|hz⟩:=all_sheets i upper x
    · exact ⟨Sum.inl z,hz.symm⟩
    · exact ⟨Sum.inr z,hz.symm⟩
lemma fromSum_open (i:Fin 4) (upper:Bool) : IsOpenMap (fromSum i upper) := by
  intro V hV
  have he:fromSum i upper '' V=
      sheet i upper true '' (Sum.inl ⁻¹' V) ∪ sheet i upper false '' (Sum.inr ⁻¹' V) := by
    ext p
    constructor
    · rintro ⟨z,hz,rfl⟩
      cases z with
      | inl z=>exact Or.inl ⟨z,hz,rfl⟩
      | inr z=>exact Or.inr ⟨z,hz,rfl⟩
    · rintro (⟨z,hz,rfl⟩|⟨z,hz,rfl⟩)
      · exact ⟨Sum.inl z,hz,rfl⟩
      · exact ⟨Sum.inr z,hz,rfl⟩
  rw [he]
  exact (sheet_open i upper true _ (hV.preimage continuous_inl)).union
    (sheet_open i upper false _ (hV.preimage continuous_inr))

/-- An actual homeomorphism, not merely a two-element fiber count, of the
whole original inverse halfplane with two copies of the same base halfplane. -/
@[expose] def homeomorph (i:Fin 4) (upper:Bool) : Half upper⊕Half upper≃ₜTotal i upper:=
  (Equiv.ofBijective (fromSum i upper) (fromSum_bijective i upper)).toHomeomorphOfContinuousOpen
    (fromSum_continuous i upper) (fromSum_open i upper)

lemma homeomorph_inl (i:Fin 4) (upper:Bool) (z:Half upper) :
    homeomorph i upper (Sum.inl z)=sheet i upper true z:=rfl
lemma homeomorph_inr (i:Fin 4) (upper:Bool) (z:Half upper) :
    homeomorph i upper (Sum.inr z)=sheet i upper false z:=rfl
lemma homeomorph_projection (i:Fin 4) (upper:Bool) (z:Half upper⊕Half upper) :
    normalizedMap i (homeomorph i upper z).val=
      ((Sum.elim (fun z:Half upper=>z.val) (fun z:Half upper=>z.val) z):OnePoint ℂ) := by
  cases z with
  | inl z=>exact sheet_projection i upper true z
  | inr z=>exact sheet_projection i upper false z
end PELOriginalHalfPlaneSheetTopology318
