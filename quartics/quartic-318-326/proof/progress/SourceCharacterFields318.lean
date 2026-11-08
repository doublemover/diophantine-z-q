module
public import CharacterQuadraticField318
public import SourceTwistArithmetic318
public section
noncomputable section
namespace SourceCharacterFields318
open Polynomial KummerTensorField318
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] def complement (i:Fin 4):Finset (Fin 4):=Finset.univ.erase i
lemma complement_nonempty (i:Fin 4) : (complement i).Nonempty:=by
  fin_cases i <;> decide
lemma complement_eq (i:Fin 4) : complement i=
    {SourceTwistArithmetic318.complement i 0,SourceTwistArithmetic318.complement i 1,
      SourceTwistArithmetic318.complement i 2}:=by
  fin_cases i <;> decide
variable (c:Fin 4→ℚˣ)
instance radicandNonsquare (i:Fin 4) :
    Fact (¬IsSquare (CharacterRoot318.radicand (SourceKummerField318.parameter c) (complement i))):=
  ⟨SourceKummerField318.product_nonsquare c _ (complement_nonempty i)⟩
@[expose] def field (i:Fin 4):IntermediateField (RatFunc ℚ) (Raw (SourceKummerField318.parameter c)):=
  CharacterQuadraticField318.field (SourceKummerField318.parameter c) (complement i)
@[expose] def twistProduct (i:Fin 4):ℚ:=∏j∈complement i,(c j:ℚ)

theorem cubic_product (i:Fin 4) :
    (∏j∈complement i,(X-C (LinearContactSquareclass318.contacts j)))=SourceTwistArithmetic318.cubic i:=by
  rw [complement_eq]
  fin_cases i <;> simp [SourceTwistArithmetic318.cubic,SourceTwistArithmetic318.complement,
    Fin.prod_univ_succ] <;> ring

/-- The actual radicand is precisely the complementary twist times the
three remaining labelled contact factors. -/
theorem radicand_cubic (i:Fin 4) :
    CharacterRoot318.radicand (SourceKummerField318.parameter c) (complement i)=
    algebraMap ℚ[X] (RatFunc ℚ) (C (twistProduct c i)*SourceTwistArithmetic318.cubic i):=by
  rw [←cubic_product]
  simp only [CharacterRoot318.radicand,SourceKummerField318.parameter,twistProduct,
    ←map_prod,Finset.prod_mul_distrib]

theorem character_root_equation (i:Fin 4) :
    CharacterRoot318.root (SourceKummerField318.parameter c) (complement i)^2=
    algebraMap (RatFunc ℚ) (Raw (SourceKummerField318.parameter c))
      (algebraMap ℚ[X] (RatFunc ℚ) (C (twistProduct c i)*SourceTwistArithmetic318.cubic i)):=
  (CharacterRoot318.root_square _ _).trans
    (congrArg (algebraMap (RatFunc ℚ) (Raw (SourceKummerField318.parameter c))) (radicand_cubic c i))

theorem degree_two (i:Fin 4) : Module.finrank (RatFunc ℚ) (field c i)=2:=
  CharacterQuadraticField318.degree_two _ _

theorem actual_fixed_field (i:Fin 4) :
    IntermediateField.fixedField (field c i).fixingSubgroup=field c i:=
  CharacterQuadraticField318.actual_fixed_field _ _

theorem sign_mem_fixing_iff (i:Fin 4) (b:Fin 4→Bool) :
    FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b∈(field c i).fixingSubgroup↔
    (∏j∈complement i,(if b j then (-1:RatFunc ℚ) else 1))=1:=
  CharacterQuadraticField318.sign_mem_fixing_iff _ _ _

theorem fixed_twist_product (i:Fin 4) :
    twistProduct SourceTwistArithmetic318.units i=SourceTwistArithmetic318.twistProducts i:=by
  unfold twistProduct
  rw [complement_eq]
  fin_cases i <;> norm_num [SourceTwistArithmetic318.units,SourceTwistArithmetic318.twistProducts,
    SourceTwistArithmetic318.constants,SourceTwistArithmetic318.complement,Fin.prod_univ_succ]

@[expose] def flip (i:Fin 4):Fin 4→Bool:=fun j=>decide (j=i)

theorem omitted_flip_fixes (i:Fin 4) :
    FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) (flip i)∈
      (field c i).fixingSubgroup:=by
  rw [sign_mem_fixing_iff]
  apply Finset.prod_eq_one
  intro j hj
  simp only [complement,Finset.mem_erase] at hj
  simp [flip,hj.1]

theorem other_flip_negates (i j:Fin 4) (hji:j≠i) :
    FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) (flip j)
      (CharacterRoot318.root (SourceKummerField318.parameter c) (complement i))=
    -CharacterRoot318.root (SourceKummerField318.parameter c) (complement i):=by
  rw [CharacterRoot318.sign_action]
  have hs:CharacterRoot318.sign (F:=RatFunc ℚ) (complement i) (flip j)=-1:=by
    simp [CharacterRoot318.sign,flip,complement,hji]
  rw [hs,map_neg,map_one]
  change -(1:Raw (SourceKummerField318.parameter c))*
    CharacterRoot318.root (SourceKummerField318.parameter c) (complement i)=_
  exact neg_one_mul (CharacterRoot318.root (SourceKummerField318.parameter c) (complement i))

theorem fixing_subgroup_card (i:Fin 4) : Nat.card (field c i).fixingSubgroup=8:=
  CharacterQuadraticField318.fixing_subgroup_card _ _
end SourceCharacterFields318
