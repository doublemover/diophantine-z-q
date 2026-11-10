module
public import PELOriginalInvolutionFiber318
public import PELOriginalInvolutionComplexAtlas318
public section
noncomputable section
namespace PELOriginalResidualDeckAction318
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalInvolutionTower318
open PELOriginalInvolutionFiber318 PELStabilizerLocusInvariant318
set_option maxHeartbeats 2400000

/-- The actual eight-word character kernel acts on the actual order-two
involution quotient, because its original action commutes with that involution. -/
@[expose] def kernelMap (i : Fin 4) (k : (character i).ker) :
    InvolutionBase i → InvolutionBase i :=
  Quotient.map' (fun x => (k:Labels) • x) (by
    rintro x y ⟨h,hh⟩
    refine ⟨h,?_⟩
    change (h:Labels) • ((k:Labels) • y)=(k:Labels) • x
    rw [action_commute,hh])
lemma kernelMap_value (i : Fin 4) (k : (character i).ker) (x : UnlevelledBase) :
    kernelMap i k (toInvolution i x)=toInvolution i ((k:Labels) • x) := rfl

@[expose] def kernelEquiv (i : Fin 4) (k : (character i).ker) : Equiv.Perm (InvolutionBase i) where
  toFun := kernelMap i k
  invFun := kernelMap i k⁻¹
  left_inv y := by
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective y
    change toInvolution i ((k:Labels)⁻¹ • ((k:Labels) • x))=toInvolution i x
    rw [inv_smul_smul]
  right_inv y := by
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective y
    change toInvolution i ((k:Labels) • ((k:Labels)⁻¹ • x))=toInvolution i x
    rw [smul_inv_smul]

@[expose] def kernelAction (i : Fin 4) : (character i).ker →* Equiv.Perm (InvolutionBase i) where
  toFun := kernelEquiv i
  map_one' := by
    ext y
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective y
    change toInvolution i ((1:Labels) • x)=toInvolution i x
    rw [one_smul]
  map_mul' k l := by
    ext y
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective y
    change toInvolution i (((k:Labels)*(l:Labels)) • x)=
      toInvolution i ((k:Labels) • ((l:Labels) • x))
    rw [mul_smul]

/-- The residual deck group is the IMAGE of that exact original action,
not a selected abstract four-element group or a supplied deck representation. -/
@[expose] def Deck (i : Fin 4) : Subgroup (Equiv.Perm (InvolutionBase i)) :=
  (kernelAction i).range
@[expose] def deckMap (i : Fin 4) : (character i).ker →* Deck i :=
  (kernelAction i).rangeRestrict
lemma deckMap_surjective (i : Fin 4) : Function.Surjective (deckMap i) := by
  rintro ⟨g,k,hk⟩
  exact ⟨k,Subtype.ext hk⟩

instance (i : Fin 4) : MulAction (Deck i) (InvolutionBase i) where
  smul g y := g.val y
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

lemma deckMap_value (i : Fin 4) (k : (character i).ker) (x : UnlevelledBase) :
    deckMap i k • toInvolution i x=toInvolution i ((k:Labels) • x) := rfl

/-- Exact kernel: precisely the old omitted-label involution, not an
extra stabilizer subgroup chosen separately on each fiber. -/
theorem deckMap_kernel (i : Fin 4) (k : (character i).ker) :
    deckMap i k=1 ↔ (k:Labels)∈involutionGroup i := by
  constructor
  · intro hk
    let x := PELOriginalLabeledFixedOrbits318.originalPoint 0
    have he := congrArg (fun g : Deck i => g • toInvolution i x) hk
    exact (residual_free i k x).mp (by simpa only [one_smul,deckMap_value] using he)
  · intro hk
    apply Subtype.ext
    apply Equiv.ext
    intro y
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective y
    exact (residual_free i k x).mpr hk

/-- The residual action is free at EVERY actual point, not merely at a
generic fiber. This is stronger than the cardinality-four result. -/
theorem deck_fixed_iff (i : Fin 4) (g : Deck i) (y : InvolutionBase i) :
    g • y=y ↔ g=1 := by
  obtain ⟨k,rfl⟩ := deckMap_surjective i g
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective y
  rw [deckMap_value,residual_free,deckMap_kernel]

instance (i : Fin 4) : IsCancelSMul (Deck i) (InvolutionBase i) :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (by
    intro g y h
    exact (deck_fixed_iff i g y).mp h)

/-- Every actual residual transformation preserves the same holomorphic
involution-to-character projection. -/
theorem deck_over_base (i : Fin 4) (g : Deck i) (y : InvolutionBase i) :
    toCharacterBase i (g • y)=toCharacterBase i y := by
  obtain ⟨k,rfl⟩ := deckMap_surjective i g
  obtain ⟨x,rfl⟩ := Quotient.mk_surjective y
  exact (toCharacter_eq_iff i _ _).mpr ⟨k,rfl⟩

/-- The entire original map fibers are the actual residual deck orbits. -/
theorem fiber_iff_orbit (i : Fin 4) (y z : InvolutionBase i) :
    toCharacterBase i y=toCharacterBase i z ↔ ∃ g : Deck i,g • z=y := by
  constructor
  · intro he
    obtain ⟨x,rfl⟩ := Quotient.mk_surjective y
    obtain ⟨w,rfl⟩ := Quotient.mk_surjective z
    obtain ⟨k,hk⟩ := (toCharacter_eq_iff i x w).mp he
    exact ⟨deckMap i k,congrArg (toInvolution i) hk⟩
  · rintro ⟨g,rfl⟩
    exact deck_over_base i g z
end PELOriginalResidualDeckAction318
