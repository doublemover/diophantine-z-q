module
public import PELOriginalInvolutionTower318
public section
noncomputable section
namespace PELOriginalInvolutionFiber318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalCharacterTopology318
open PELOriginalInvolutionTower318
set_option maxHeartbeats 1600000

@[expose] def kernelInvolution (i : Fin 4) : (character i).ker :=
  ⟨involution i,involution_character i⟩
lemma kernelInvolution_ne_one (i : Fin 4) : kernelInvolution i ≠ 1 := by
  intro h
  exact involution_ne_one i (congrArg Subtype.val h)

/-- Equality in an original involution quotient is EXACTLY the two-element
coset relation on the original eight-word kernel, at every original point. -/
lemma orbit_pair (i : Fin 4) (k l : (character i).ker) (x : UnlevelledBase) :
    toInvolution i ((k : Labels) • x) = toInvolution i ((l : Labels) • x) ↔
      k = l ∨ k = kernelInvolution i * l := by
  have hh := residual_free i (k * l⁻¹) ((l : Labels) • x)
  simp only [Subgroup.coe_mul,Subgroup.coe_inv,mul_smul,inv_smul_smul] at hh
  rw [hh]
  change ((k : Labels) * (l : Labels)⁻¹ = 1 ∨
    (k : Labels) * (l : Labels)⁻¹ = involution i) ↔ _
  constructor
  · rintro (he | he)
    · left
      apply Subtype.ext
      have h := congrArg (fun g : Labels => g * (l : Labels)) he
      simpa only [mul_assoc,inv_mul_cancel,mul_one,one_mul] using h
    · right
      apply Subtype.ext
      have h := congrArg (fun g : Labels => g * (l : Labels)) he
      simpa only [mul_assoc,inv_mul_cancel,mul_one] using h
  · rintro (rfl | rfl)
    · exact Or.inl (mul_inv_cancel _)
    · exact Or.inr (by
        change (involution i * (l : Labels)) * (l : Labels)⁻¹ = involution i
        rw [mul_assoc,mul_inv_cancel,mul_one])

abbrev Fiber (i : Fin 4) (x : UnlevelledBase) :=
  {y : InvolutionBase i // toCharacterBase i y = toCharacter i x}

@[expose] def toFiber (i : Fin 4) (x : UnlevelledBase) (k : (character i).ker) : Fiber i x :=
  ⟨toInvolution i ((k : Labels) • x),
    (toCharacter_eq_iff i _ _).mpr ⟨k,rfl⟩⟩

lemma toFiber_surjective (i : Fin 4) (x : UnlevelledBase) :
    Function.Surjective (toFiber i x) := by
  rintro ⟨y,hy⟩
  obtain ⟨z,rfl⟩ := Quotient.mk_surjective y
  obtain ⟨k,hk⟩ := (toCharacter_eq_iff i z x).mp hy
  refine ⟨k,?_⟩
  apply Subtype.ext
  exact congrArg (toInvolution i) hk

lemma toFiber_equal (i : Fin 4) (x : UnlevelledBase) (k l : (character i).ker) :
    toFiber i x k = toFiber i x l ↔ k = l ∨ k = kernelInvolution i * l := by
  rw [Subtype.ext_iff]
  exact orbit_pair i k l x

lemma toFiber_fiber_card (i : Fin 4) (x : UnlevelledBase) (y : Fiber i x) :
    Nat.card {k : (character i).ker // toFiber i x k = y} = 2 := by
  obtain ⟨l,rfl⟩ := toFiber_surjective i x y
  have he : {k : (character i).ker | toFiber i x k = toFiber i x l} =
      {l,kernelInvolution i * l} := by
    ext k
    exact toFiber_equal i x k l
  have hn : l ≠ kernelInvolution i * l := by
    intro h
    apply kernelInvolution_ne_one i
    have he : kernelInvolution i * l = 1 * l := h.symm.trans (one_mul l).symm
    exact mul_right_cancel he
  rw [Nat.card_coe_set_eq,he,Set.ncard_pair hn]

/-- Every actual involution-to-character fiber has FOUR points. No
unramified-fiber hypothesis, genus-one group law, or elliptic isogeny theorem
is used; the full original stabilizer exclusion supplies the count. -/
theorem degree_four_everywhere (i : Fin 4) (x : UnlevelledBase) :
    Nat.card (Fiber i x) = 4 := by
  classical
  letI : Finite (Fiber i x) := Finite.of_surjective (toFiber i x) (toFiber_surjective i x)
  letI : Fintype (Fiber i x) := Fintype.ofFinite _
  have h := Fintype.card_congr (Equiv.sigmaFiberEquiv (toFiber i x)).symm
  rw [Fintype.card_sigma] at h
  have hf : ∀ y : Fiber i x,Fintype.card {k : (character i).ker // toFiber i x k = y} = 2 := by
    intro y
    simpa only [Nat.card_eq_fintype_card] using toFiber_fiber_card i x y
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul] at h
  have hk := kernel_card i
  rw [Nat.card_eq_fintype_card]
  omega

/-- The count covers every point of the actual intermediate target. -/
theorem every_fiber_four (i : Fin 4) (q : CharacterBase i) :
    Nat.card {y : InvolutionBase i // toCharacterBase i y = q} = 4 := by
  obtain ⟨x,rfl⟩ := toCharacter_surjective i q
  exact degree_four_everywhere i x
end PELOriginalInvolutionFiber318
