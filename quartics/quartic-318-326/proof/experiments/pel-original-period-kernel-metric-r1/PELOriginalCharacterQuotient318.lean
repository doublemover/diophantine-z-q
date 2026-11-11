module
public import PELOriginalGenusBranchSqueeze318
public section
noncomputable section
namespace PELOriginalCharacterQuotient318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalBranchLabels318 PELOriginalLabeledFixedOrbits318
open PELOriginalFiniteRamification318 PELStabilizerLocusInvariant318
set_option maxHeartbeats 1200000

/-- The literal prime-exponent character of the ORIGINAL sixteen-word group.
The four characters are not chosen from an unrelated abstract action. -/
@[expose] def character (i : Fin 4) : Labels →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (Multiplicative.toAdd g i)
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def toggle (i : Fin 4) : Labels :=
  Multiplicative.ofAdd (fun j => if j = i then 1 else 0)

lemma toggle_nontrivial (i : Fin 4) : character i (toggle i) ≠ 1 := by
  change Multiplicative.ofAdd (if i = i then (1 : ZMod 2) else 0) ≠ 1
  simp

lemma character_cases : ∀ (i : Fin 4) (g : Labels),
    character i g = 1 ∨ character i g = character i (toggle i) := by decide

/-- The actual intermediate quotient by the full kernel of this character. -/
abbrev CharacterBase (i : Fin 4) :=
  Quotient (MulAction.orbitRel (character i).ker UnlevelledBase)
@[expose] def toCharacter (i : Fin 4) : UnlevelledBase → CharacterBase i := Quotient.mk _

lemma toCharacter_eq_iff (i : Fin 4) (x y : UnlevelledBase) :
    toCharacter i x = toCharacter i y ↔
      ∃ g : (character i).ker, (g : Labels) • y = x := by
  constructor
  · exact Quotient.exact
  · exact Quotient.sound

/-- Forgetting only the character level lands in the SAME original maximal quotient. -/
@[expose] def toMaximal (i : Fin 4) : CharacterBase i → MaximalBase :=
  Quotient.lift PELOriginalMaximalQuotient318.projection (by
    intro x y h
    obtain ⟨g, hg⟩ := h
    exact (PELOriginalMaximalQuotient318.projection_eq_iff x y).mpr ⟨g.val, hg⟩)

lemma original_square (i : Fin 4) (x : UnlevelledBase) :
    toMaximal i (toCharacter i x) = PELOriginalMaximalQuotient318.projection x := rfl

lemma same_character (i : Fin 4) (g h : Labels) (x : UnlevelledBase)
    (he : character i g = character i h) :
    toCharacter i (g • x) = toCharacter i (h • x) := by
  apply (toCharacter_eq_iff i _ _).mpr
  refine ⟨⟨g * h⁻¹, ?_⟩, ?_⟩
  · change character i (g * h⁻¹) = 1
    simp only [map_mul, map_inv, he, mul_inv_cancel]
  · change (g * h⁻¹) • (h • x) = g • x
    rw [mul_smul, inv_smul_smul]

/-- This criterion uses the whole ORIGINAL stabilizer, not a selected inertia element. -/
lemma stabilizer_character (i : Fin 4) (g : Labels) (x : UnlevelledBase) :
    toCharacter i (g • x) = toCharacter i x ↔
      ∃ h : Labels, h • x = x ∧ character i h = character i g := by
  constructor
  · intro he
    obtain ⟨k, hk⟩ := (toCharacter_eq_iff i _ _).mp he
    refine ⟨(k : Labels)⁻¹ * g, ?_, ?_⟩
    · rw [mul_smul, ← hk, inv_smul_smul]
    · have hkχ : character i (k : Labels) = 1 := k.property
      simp only [map_mul, map_inv, hkχ, inv_one, one_mul]
  · rintro ⟨h, hf, he⟩
    simpa only [hf] using same_character i g h x he.symm

/-- Every actual fiber is the literal pair of the two original character cosets.
This includes ramified fibers, when the two points coincide. -/
lemma full_fiber_pair (i : Fin 4) (x : UnlevelledBase) :
    {y : CharacterBase i | toMaximal i y = PELOriginalMaximalQuotient318.projection x} =
      {toCharacter i x, toCharacter i (toggle i • x)} := by
  ext y
  refine Quotient.inductionOn y ?_
  intro z
  constructor
  · intro he
    obtain ⟨g, rfl⟩ := (PELOriginalMaximalQuotient318.projection_eq_iff z x).mp he
    rcases character_cases i g with hg | hg
    · left
      simpa only [one_smul] using same_character i g 1 x (hg.trans (map_one (character i)).symm)
    · right
      exact same_character i g (toggle i) x hg
  · rintro (he | he)
    · exact congrArg (toMaximal i) he
    · have hproj : PELOriginalMaximalQuotient318.projection (toggle i • x) =
          PELOriginalMaximalQuotient318.projection x :=
        (PELOriginalMaximalQuotient318.projection_eq_iff _ _).mpr ⟨toggle i, rfl⟩
      exact (congrArg (toMaximal i) he).trans hproj

lemma fiber_card (i : Fin 4) (x : UnlevelledBase) :
    Nat.card {y : CharacterBase i // toMaximal i y =
      PELOriginalMaximalQuotient318.projection x} =
      if toCharacter i x = toCharacter i (toggle i • x) then 1 else 2 := by
  classical
  rw [Nat.card_coe_set_eq, full_fiber_pair]
  by_cases he : toCharacter i x = toCharacter i (toggle i • x)
  · simp [he]
  · rw [Set.ncard_pair he, if_neg he]

/-- Away from the full original branch locus each intermediate fiber has two points. -/
lemma regular_fiber_card (i : Fin 4) (x : UnlevelledBase)
    (hx : x ∉ nontrivialStabilizerLocus) :
    Nat.card {y : CharacterBase i // toMaximal i y =
      PELOriginalMaximalQuotient318.projection x} = 2 := by
  rw [fiber_card, if_neg]
  intro he
  obtain ⟨g, hg, hχ⟩ := (stabilizer_character i (toggle i) x).mp he.symm
  apply hx
  refine ⟨Multiplicative.toAdd g, ?_, hg⟩
  intro hzero
  have hg1 : g = 1 := congrArg Multiplicative.ofAdd hzero
  have hh := hχ
  rw [hg1, map_one] at hh
  exact toggle_nontrivial i hh.symm

/-- At an original labeled branch point the intermediate double quotient
ramifies precisely when the original character sees that label. -/
lemma branch_pair_eq (i : Fin 4) (j : Fin 5) (x : UnlevelledBase)
    (hx : x ∈ fixedLocus j) :
    toCharacter i (toggle i • x) = toCharacter i x ↔
      character i (Multiplicative.ofAdd (InertiaLabels318.fiveLabels j)) ≠ 1 := by
  rw [stabilizer_character]
  constructor
  · rintro ⟨g, hg, hχ⟩
    rcases (locus_stabilizer_iff j x hx (Multiplicative.toAdd g)).mp hg with h0 | hj
    · have hg1 : g = 1 := congrArg Multiplicative.ofAdd h0
      rw [hg1, map_one] at hχ
      exact False.elim (toggle_nontrivial i hχ.symm)
    · have hglabel : g = Multiplicative.ofAdd (InertiaLabels318.fiveLabels j) :=
        congrArg Multiplicative.ofAdd hj
      rw [hglabel] at hχ
      exact fun he => toggle_nontrivial i (hχ.symm.trans he)
  · intro hne
    refine ⟨Multiplicative.ofAdd (InertiaLabels318.fiveLabels j), hx, ?_⟩
    exact (character_cases i _).resolve_left hne

lemma branch_fiber_card (i : Fin 4) (j : Fin 5) (x : UnlevelledBase)
    (hx : x ∈ fixedLocus j) :
    Nat.card {y : CharacterBase i // toMaximal i y =
      PELOriginalMaximalQuotient318.projection x} =
      if InertiaLabels318.fiveLabels j i = 0 then 2 else 1 := by
  classical
  rw [fiber_card]
  have h := branch_pair_eq i j x hx
  have hc : character i (Multiplicative.ofAdd (InertiaLabels318.fiveLabels j)) = 1 ↔
      InertiaLabels318.fiveLabels j i = 0 := Iff.rfl
  by_cases hz : InertiaLabels318.fiveLabels j i = 0
  · rw [if_pos hz, if_neg]
    intro he
    exact (h.mp he.symm) (hc.mpr hz)
  · rw [if_neg hz, if_pos ((h.mpr (fun he => hz (hc.mp he))).symm)]
end PELOriginalCharacterQuotient318
