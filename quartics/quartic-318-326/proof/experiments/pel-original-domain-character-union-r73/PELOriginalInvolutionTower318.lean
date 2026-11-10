module
public import PELOriginalContactCharacterIdentity318
public section
noncomputable section
namespace PELOriginalInvolutionTower318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalCharacterBranches318
open PELOriginalBranchLabels318
set_option maxHeartbeats 1600000

@[expose] def involution (i : Fin 4) : Labels :=
  Multiplicative.ofAdd (InertiaLabels318.fiveLabels (omitted i))
lemma involution_ne_one (i : Fin 4) : involution i ≠ 1 := by
  intro h
  exact InertiaLabels318.five_labels_nonzero (omitted i)
    (congrArg Multiplicative.toAdd h)
lemma involution_square : ∀ i : Fin 4, involution i * involution i = 1 := by decide
lemma involution_inv : ∀ i : Fin 4, (involution i)⁻¹ = involution i := by decide
lemma involution_character (i : Fin 4) : character i (involution i) = 1 := by
  change Multiplicative.ofAdd (InertiaLabels318.fiveLabels (omitted i) i) = 1
  rw [(omitted_label i (omitted i)).mpr rfl]
  rfl

/-- The actual order-two subgroup defining the PUBLISHED genus-one
quotient. It is not the eight-element character kernel. -/
@[expose] def involutionGroup (i : Fin 4) : Subgroup Labels where
  carrier := {g | g = 1 ∨ g = involution i}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl)
    · exact Or.inl (one_mul _)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl (involution_square i)
  inv_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (involution_inv i)

lemma involutionGroup_le (i : Fin 4) : involutionGroup i ≤ (character i).ker := by
  rintro g (rfl | rfl)
  · exact (character i).ker.one_mem
  · exact involution_character i

/-- Every actual stabilizer inside the eight-word kernel is contained
in the same old order-two subgroup, at EVERY point of the original curve. -/
lemma kernel_fixed_mem (i : Fin 4) (k : (character i).ker) (x : UnlevelledBase)
    (hk : k • x = x) : (k : Labels) ∈ involutionGroup i := by
  by_cases h1 : (k : Labels) = 1
  · exact Or.inl h1
  · have hn : Multiplicative.toAdd (k : Labels) ≠ 0 := by
      intro hz
      exact h1 (congrArg Multiplicative.ofAdd hz)
    obtain ⟨j,hj⟩ := original_fixed_label _ x hn hk
    have hlabel : (k : Labels) = Multiplicative.ofAdd (InertiaLabels318.fiveLabels j) :=
      congrArg Multiplicative.ofAdd hj
    have hχ : character i (k : Labels) = 1 := k.property
    rw [hlabel] at hχ
    have hz : InertiaLabels318.fiveLabels j i = 0 := congrArg Multiplicative.toAdd hχ
    have hjomit := (omitted_label i j).mp hz
    exact Or.inr (hlabel.trans (congrArg (fun j => Multiplicative.ofAdd
      (InertiaLabels318.fiveLabels j)) hjomit))

abbrev InvolutionBase (i : Fin 4) :=
  Quotient (MulAction.orbitRel (involutionGroup i) UnlevelledBase)
@[expose] def toInvolution (i : Fin 4) : UnlevelledBase → InvolutionBase i := Quotient.mk _
lemma toInvolution_eq_iff (i : Fin 4) (x y : UnlevelledBase) :
    toInvolution i x = toInvolution i y ↔
      ∃ h : involutionGroup i, (h : Labels) • y = x := by
  constructor
  · exact Quotient.exact
  · exact Quotient.sound

/-- The actual published-involution quotient maps to the character quotient
by the true subgroup inclusion, not by an assumed isomorphism of elliptic curves. -/
@[expose] def toCharacterBase (i : Fin 4) : InvolutionBase i → CharacterBase i :=
  Quotient.lift (toCharacter i) (by
    intro x y he
    obtain ⟨h,hh⟩ := he
    exact (toCharacter_eq_iff i x y).mpr
      ⟨⟨h.val,involutionGroup_le i h.property⟩,hh⟩)
lemma original_square (i : Fin 4) (x : UnlevelledBase) :
    toCharacterBase i (toInvolution i x) = toCharacter i x := rfl

/-- The residual kernel/order-two action has NO fixed point: an actual
kernel word preserves an involution-quotient point exactly when it already
belongs to the old involution subgroup. No genus-one group law is assumed. -/
lemma residual_free (i : Fin 4) (k : (character i).ker) (x : UnlevelledBase) :
    toInvolution i ((k : Labels) • x) = toInvolution i x ↔
      (k : Labels) ∈ involutionGroup i := by
  constructor
  · intro he
    obtain ⟨h,hh⟩ := (toInvolution_eq_iff i _ _).mp he
    let hK : (character i).ker := ⟨h.val,involutionGroup_le i h.property⟩
    let u : (character i).ker := hK⁻¹ * k
    have hu : u • x = x := by
      change ((h : Labels)⁻¹ * (k : Labels)) • x = x
      rw [mul_smul,← hh,inv_smul_smul]
    have humem := kernel_fixed_mem i u x hu
    have hprod := (involutionGroup i).mul_mem h.property humem
    change (h : Labels) * ((h : Labels)⁻¹ * (k : Labels)) ∈ involutionGroup i at hprod
    simpa only [mul_inv_cancel_left] using hprod
  · intro hk
    exact (toInvolution_eq_iff i _ _).mpr ⟨⟨k.val,hk⟩,rfl⟩
end PELOriginalInvolutionTower318
