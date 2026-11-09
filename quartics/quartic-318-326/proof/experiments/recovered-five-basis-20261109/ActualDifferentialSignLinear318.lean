module
public import ActualFiveRationalIndependent318
public import ContactGlobalSignAction318
public import ContactGlobalCoefficientScalars318
public import CharacterDifferentialInvariants318

public section
noncomputable section
namespace ActualDifferentialSignLinear318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open ActualFiveRationalIndependent318
open IntrinsicDifferentialPullback318 IntrinsicDifferentialFunctor318
attribute [local instance] rationalModule
set_option maxHeartbeats 600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

abbrev p := ContactIntrinsicDifferentials318.structureMap units
abbrev xor (b d : Fin 4 → Bool) : Fin 4 → Bool := fun i => Bool.xor (b i) (d i)
abbrev zeroSign : Fin 4 → Bool := fun _ => false

/-- The actual whole-scheme sign pullback, linear for the original source
structural rational action. -/
@[expose] def action (b : Fin 4 → Bool) : G →ₗ[ℚ] G where
  __ := ContactDifferentialCharacters318.action b
  map_smul' a s := StructuralConstantPullback318.globalSection_constant_smul
    (ContactGlobalSigns318.map units b) p p (ContactDifferentialCharacters318.over_Q b) a s

lemma action_apply (b : Fin 4 → Bool) (s : G) :
    action b s = ContactDifferentialCharacters318.action b s := rfl

theorem action_zero (s : G) : action zeroSign s = s := by
  change globalSection (ContactGlobalSigns318.map units zeroSign) p p _ s = s
  rw [globalSection_congr (ContactGlobalSignAction318.identity units) p p _ (Category.id_comp p)]
  exact globalSection_id p (Category.id_comp p) s

theorem action_comp (b d : Fin 4 → Bool) (s : G) :
    action b (action d s) = action (xor b d) s := by
  let f := ContactGlobalSigns318.map units b
  let g := ContactGlobalSigns318.map units d
  have hfg : (f ≫ g) ≫ p = p := by
    rw [Category.assoc, ContactDifferentialCharacters318.over_Q,
      ContactDifferentialCharacters318.over_Q]
  change globalSection f p p _ (globalSection g p p _ s) = _
  rw [← globalSection_comp f g p p p _ _ hfg]
  exact globalSection_congr (ContactGlobalSignAction318.composition units b d)
    p p hfg (ContactDifferentialCharacters318.over_Q (xor b d)) s

theorem involution (b : Fin 4 → Bool) (s : G) : action b (action b s) = s := by
  rw [action_comp]
  have h : xor b b = zeroSign := by funext i; simp [xor, zeroSign]
  rw [h, action_zero]

theorem flip_character (i j : Fin 4) :
    action (SourceCharacterFields318.flip i) (ContactCharacterDifferentials318.differential j) =
      if i = j then ContactCharacterDifferentials318.differential j
      else -ContactCharacterDifferentials318.differential j := by
  change ContactDifferentialCharacters318.action _ _ = _
  by_cases h : i = j
  · subst j
    rw [ite_eq_left rfl]
    exact ContactDifferentialCharacters318.positive i _
      (CharacterDifferentialInvariants318.omitted_flip_positive i)
  · rw [ite_eq_right h]
    apply ContactDifferentialCharacters318.negative
    fin_cases i <;> fin_cases j <;>
      norm_num [CharacterBooleanAffine318.epsilon, SourceCharacterFields318.complement,
        SourceCharacterFields318.flip] at *

@[expose] def part (b : Fin 4 → Bool) (i : Fin 4) : Fin 4 → Bool :=
  if b i then SourceCharacterFields318.flip i else zeroSign

lemma sign_decomposition (b : Fin 4 → Bool) :
    b = xor (part b 0) (xor (part b 1) (xor (part b 2) (part b 3))) := by
  funext i
  fin_cases i <;> simp [xor, part, ite_apply, SourceCharacterFields318.flip, zeroSign]

/-- Being anti-invariant under each of the four actual generators gives
the full-root character on every original sign. -/
theorem full_character_of_flips (s : G)
    (h : ∀ i, action (SourceCharacterFields318.flip i) s = -s) (b : Fin 4 → Bool) :
    action b s = FifthOpenSigns318.epsilon b • s := by
  have hp (i : Fin 4) : action (part b i) s = (if b i then (-1 : ℚ) else 1) • s := by
    cases hb : b i <;> simp only [part, hb, Bool.false_eq_true, ite_false, ite_true]
    · rw [action_zero, one_smul]
    · rw [h, neg_one_smul]
  conv_lhs => rw [sign_decomposition b]
  rw [← action_comp, ← action_comp, ← action_comp]
  simp only [hp, map_smul, smul_smul, FifthOpenSigns318.epsilon, Fin.prod_univ_succ]
  congr 1
  change (if b 3 then (-1 : ℚ) else 1) * (if b 2 then -1 else 1) *
      (if b 1 then -1 else 1) * (if b 0 then -1 else 1) =
    (if b 0 then -1 else 1) * ((if b 1 then -1 else 1) *
      ((if b 2 then -1 else 1) * ((if b 3 then -1 else 1) * 1)))
  ring

end ActualDifferentialSignLinear318
