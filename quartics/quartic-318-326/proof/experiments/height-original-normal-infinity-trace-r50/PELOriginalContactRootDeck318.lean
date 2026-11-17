module
public import PELOriginalContactRootFunctions318
public import PELOriginalContactCharacterIdentity318
public section
noncomputable section
namespace PELOriginalContactRootDeck318
open Set
open PELUnlevelledComplexBase318 PELOriginalMaximalQuotient318
open PELOriginalCharacterQuotient318 PELOriginalContactRootFunctions318
open PELOriginalCommonContactBase318 FourCharacterRootRecombination318
open FourBinaryCharacters318 OriginalContactInertiaBasis318

lemma original_projection (g:Labels) (x:UnlevelledBase):
    PELOriginalMaximalQuotient318.projection (g • x)=PELOriginalMaximalQuotient318.projection x:=
  (PELOriginalMaximalQuotient318.projection_eq_iff _ _).mpr ⟨g,rfl⟩
lemma original_regular (g:Labels) (x:UnlevelledBase) (hx:x∈RegularSource):
    g • x∈RegularSource:=by
  change PELOriginalMaximalQuotient318.projection (g • x)∉_
  rw [original_projection]
  exact hx
lemma base_action (g:Labels) (x:UnlevelledBase):base (g • x)=base x:=by
  unfold base PELOriginalContactBranchSquare318.normalizedMap
  simp only [Function.comp_apply,original_projection]

/-- The original prime character acts on the actual common cubic
ordinate through the SAME original toggle, not through an invented deck. -/
lemma ordinate_action (g:Labels) (x:UnlevelledBase) (hx:x∈RegularSource) (i:Fin 4):
    PELOriginalCommonCubicCoordinate318.ordinate i (toCharacter i (g • x))=
      complementary (F:=ℂ) i (basis g)*
        PELOriginalCommonCubicCoordinate318.ordinate i (toCharacter i x) := by
  let xf:PELOriginalRegularCharacterProduct318.CharacterFiber (basePoint (base x)) i:=
    ⟨toCharacter i x,original_base x hx⟩
  have hr:=PELOriginalCommonCubicFiberEquiv318.fiber_regular (base x) (denominator_ne x hx) i xf
  rw [PELOriginalContactCharacterIdentity318.field_character]
  rcases character_cases i g with hg|hg
  · have hz:Multiplicative.toAdd g i=0:=congrArg Multiplicative.toAdd hg
    have he:toCharacter i (g • x)=toCharacter i x:=by
      simpa only [one_smul] using same_character i g 1 x (hg.trans (map_one _).symm)
    rw [if_pos hz,one_mul,he]
  · have hz:Multiplicative.toAdd g i=1:=by
      simpa [character,toggle] using congrArg Multiplicative.toAdd hg
    have he:toCharacter i (g • x)=PELOriginalCharacterDeck318.deck i (toCharacter i x):=
      same_character i g (toggle i) x hg
    rw [if_neg (by rw [hz];norm_num),neg_one_mul,he]
    exact PELOriginalCommonCubicFibers318.ordinate_deck i _ hr

lemma triple_mul (a v:Fin 4→ℂ) (i:Fin 4):
    triple (fun k=>a k*v k) i=triple a i*triple v i:=by
  fin_cases i <;> simp only [triple,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.cons_val_three] <;> ring

/-- The inverse-inertia triple operation recovers the original ROOT
character, with the actual omitted-character ordering retained. -/
lemma triple_complementary (w:FourBinaryCharacters318.Group) (i:Fin 4):
    triple (fun k=>complementary (F:=ℂ) k w) i=coordinate (F:=ℂ) i w := by
  fin_cases i <;>
    simp [triple,complementary,coordinate,SourceTwistArithmetic318.complement,
      Fin.prod_univ_succ] <;> split_ifs <;> norm_num


/-- Full original sixteen-word deck equivariance of the SAME root
functions. This identifies each actual finite inertia with its literal
single-root flip, rather than merely matching abstract group orders. -/
theorem roots_action (g:Labels) (x:UnlevelledBase) (hx:x∈RegularSource) (i:Fin 4):
    roots (g • x) i=coordinate (F:=ℂ) i (basis g)*roots x i := by
  have he:(fun k=>PELOriginalCommonCubicCoordinate318.ordinate k (toCharacter k (g • x)))=
      (fun k=>complementary (F:=ℂ) k (basis g)*
        PELOriginalCommonCubicCoordinate318.ordinate k (toCharacter k x)):=
    funext (ordinate_action g x hx)
  unfold roots
  rw [he,base_action,triple_mul,triple_complementary]
  ring

/-- Original finite labels105,70,42,30 are exactly the four individual
root flips; no additional permutation is left for downstream arithmetic. -/
theorem finite_inertia (j:Fin 4) (x:UnlevelledBase) (hx:x∈RegularSource) (i:Fin 4):
    roots (Multiplicative.ofAdd (InertiaLabels318.labels (reverse j)) • x) i=
      (if i=j then -1 else 1)*roots x i := by
  rw [roots_action _ x hx,basis_finite]
  by_cases h:i=j <;> simp [coordinate,flip,h]
end PELOriginalContactRootDeck318
