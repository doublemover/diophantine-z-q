module
public import FifthGlobalCharacters318
public import FifthSignCharacter318
public import ContactGlobalSignFaithful318
public section
noncomputable section
namespace FifthFixingSigns318
open AlgebraicGeometry CategoryTheory SourceTwistArithmetic318
open scoped BigOperators
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
@[expose] def signs:Finset (Fin 4→Bool):=Finset.univ.filter (fun b=>FifthOpenSigns318.epsilon b=1)
theorem cardinality:signs.card=8:=by
  unfold signs FifthOpenSigns318.epsilon
  decide +kernel
lemma sign_matches (b:Fin 4→Bool):FifthSignAffine318.sign b=
    algebraMap ℚ (RatFunc ℚ) (FifthOpenSigns318.epsilon b):=by
  change (∏i:Fin 4,if b i then (-1:RatFunc ℚ) else 1)=
    algebraMap ℚ (RatFunc ℚ) (∏i:Fin 4,if b i then -1 else 1)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  split_ifs <;> simp only [map_neg,map_one]
/-- The eight selected signs are exactly the root signs fixing the whole
actual completed fifth map; this is not a fixed-point condition. -/
theorem mem_iff_fixed (b:Fin 4→Bool):b∈signs ↔
    ContactGlobalSigns318.map units b≫FifthCompletedGlobal318.map=FifthCompletedGlobal318.map:=by
  simp only [signs,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [FifthSignCharacter318.fixed_iff,sign_matches]
  constructor
  · intro h;rw [h,map_one]
  · intro h
    apply (algebraMap ℚ (RatFunc ℚ)).injective
    simpa only [map_one] using h
theorem maps_injective:Function.Injective
    (fun b:{b:Fin 4→Bool //b∈signs}=>ContactGlobalSigns318.map units b.val):=by
  intro b d h
  exact Subtype.ext (ContactGlobalSignFaithful318.injective units h)
/-- Exact finite character sum over all eight actual fixing signs. -/
theorem complementary_sum (i:Fin 4):∑b∈signs,CharacterBooleanAffine318.epsilon i b=0:=by
  unfold signs FifthOpenSigns318.epsilon CharacterBooleanAffine318.epsilon SourceCharacterFields318.complement
  fin_cases i <;> decide +kernel
theorem full_sum:∑b∈signs,FifthOpenSigns318.epsilon b=8:=by
  unfold signs FifthOpenSigns318.epsilon
  decide +kernel
end FifthFixingSigns318
