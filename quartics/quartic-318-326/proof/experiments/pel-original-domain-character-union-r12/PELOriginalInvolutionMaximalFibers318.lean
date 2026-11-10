module
public import PELOriginalResidualDeckHolomorphy318
public import PELOriginalDirectCharacterBranches318
public section
noncomputable section
namespace PELOriginalInvolutionMaximalFibers318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalCharacterTopology318
open PELOriginalInvolutionTower318 PELOriginalInvolutionLocalCover318
open PELOriginalInvolutionFiber318 PELOriginalResidualDeckAction318 PELOriginalResidualDeckFibers318
open PELOriginalCharacterBranches318 (CharacterBranchValues)
set_option maxHeartbeats 2400000

/-- The original order-two quotient's map to the actual maximal quotient;
its degree is eight, NOT the degree-two character map or level-three j-map. -/
@[expose] def toOriginalMaximal (i : Fin 4) : InvolutionBase i → MaximalBase :=
  toMaximal i ∘ toCharacterBase i
abbrev CharacterFiber (i : Fin 4) (q : MaximalBase) :=
  {y : CharacterBase i // toMaximal i y=q}
abbrev InvolutionFiber (i : Fin 4) (q : MaximalBase) :=
  {y : InvolutionBase i // toOriginalMaximal i y=q}

instance characterFiberFinite (i : Fin 4) (q : MaximalBase) : Finite (CharacterFiber i q) := by
  obtain ⟨x,rfl⟩ := PELOriginalMaximalQuotient318.projection_surjective q
  have hf : {y : CharacterBase i | toMaximal i y=PELOriginalMaximalQuotient318.projection x}.Finite := by
    rw [full_fiber_pair]
    exact Set.finite_pair _ _
  exact hf.to_subtype
instance involutionCharacterFiberFinite (i : Fin 4) (q : CharacterBase i) :
    Finite {y : InvolutionBase i // toCharacterBase i y=q} := by
  obtain ⟨y,rfl⟩ := toCharacterBase_surjective i q
  exact Finite.of_equiv (Deck i) (fiberEquiv i y)

/-- Genuine full-fiber decomposition for the original tower, with both
projections retained. It does not multiply degrees as a bare numerical premise. -/
@[expose] def fiberDecomposition (i : Fin 4) (q : MaximalBase) :
    InvolutionFiber i q ≃ Σ y : CharacterFiber i q,
      {z : InvolutionBase i // toCharacterBase i z=y.val} where
  toFun z := ⟨⟨toCharacterBase i z.val,z.property⟩,⟨z.val,rfl⟩⟩
  invFun z := ⟨z.2.val,by change toMaximal i (toCharacterBase i z.2.val)=q; rw [z.2.property]; exact z.1.property⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨y,hy⟩,⟨z,hz⟩⟩
    dsimp at hz
    subst y
    rfl

instance involutionFiberFinite (i : Fin 4) (q : MaximalBase) : Finite (InvolutionFiber i q) :=
  Finite.of_equiv _ (fiberDecomposition i q).symm

theorem full_fiber_card (i : Fin 4) (q : MaximalBase) :
    Nat.card (InvolutionFiber i q)=4*Nat.card (CharacterFiber i q) := by
  classical
  letI : Fintype (CharacterFiber i q) := Fintype.ofFinite _
  letI (y : CharacterFiber i q) : Fintype {z : InvolutionBase i // toCharacterBase i z=y.val} := Fintype.ofFinite _
  letI : Fintype (InvolutionFiber i q) := Fintype.ofFinite _
  have h := Fintype.card_congr (fiberDecomposition i q)
  rw [Fintype.card_sigma] at h
  have hf (y : CharacterFiber i q) : Fintype.card {z : InvolutionBase i // toCharacterBase i z=y.val}=4 := by
    simpa only [Nat.card_eq_fintype_card] using every_fiber_four i y.val
  simp only [hf,Finset.sum_const,Finset.card_univ,smul_eq_mul] at h
  simpa only [Nat.card_eq_fintype_card,mul_comm] using h

/-- Over every actual target point the original involution quotient has
four points precisely at the four visible branch values, and eight otherwise. -/
theorem actual_fiber_card (i : Fin 4) (q : MaximalBase) :
    Nat.card (InvolutionFiber i q)=if q∈CharacterBranchValues i then 4 else 8 := by
  classical
  rw [full_fiber_card]
  by_cases hq : q∈CharacterBranchValues i
  · rw [if_pos hq]
    have hc : Nat.card (CharacterFiber i q)=1 := hq
    rw [hc]
    norm_num
  · have hne : Nat.card (CharacterFiber i q)≠1 := hq
    have hc : Nat.card (CharacterFiber i q)=2 := by
      obtain ⟨x,rfl⟩ := PELOriginalMaximalQuotient318.projection_surjective q
      have h := fiber_card i x
      split_ifs at h <;> omega
    rw [if_neg hq,hc]
    norm_num
end PELOriginalInvolutionMaximalFibers318
