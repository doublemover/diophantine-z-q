module
public import FifthCharacterField318
public section
noncomputable section
namespace FifthCharacterDistinct318
open FifthCharacterField318 SourceTwistArithmetic318
set_option maxHeartbeats 500000
lemma flip_sign (i:Fin 4) :
    (∏ j:Fin 4, (if SourceCharacterFields318.flip i j then (-1:K) else 1))=-1 := by
  fin_cases i <;> norm_num [SourceCharacterFields318.flip,Fin.prod_univ_succ]

theorem field_ne_complement (i:Fin 4) : field ≠ SourceCharacterFields318.field units i := by
  intro h
  have hf:=SourceCharacterFields318.omitted_flip_fixes units i
  rw [←h,sign_mem_fixing_iff,flip_sign] at hf
  norm_num at hf

theorem each_flip_negates (i:Fin 4) :
    FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter units)
      (SourceCharacterFields318.flip i) root = -root := by
  rw [root,CharacterRoot318.sign_action]
  have hs: CharacterRoot318.sign (F:=K) support (SourceCharacterFields318.flip i)=-1 := flip_sign i
  rw [hs,map_neg,map_one]
  change -(1:L)*CharacterRoot318.root (SourceKummerField318.parameter units) support = _
  exact neg_one_mul (CharacterRoot318.root (SourceKummerField318.parameter units) support)
end FifthCharacterDistinct318
