module
public import SourceHOneCharacterIndices318
public import ContactFinitePoleReduction318
public import SourceSignFieldComparison318

public section
noncomputable section
namespace SourceHOneCharacterRepresentatives318
attribute [-instance] DivisionRing.toRatAlgebra
open SourceHOneCharacterIndices318 InfinityFieldCoordinates318
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (c : Fin 4 → ℚˣ)
local instance originalField : Field (L c) := (KummerTensorField318.source_raw_field c).toField

@[expose] def representative (i : Index) : ContactKummerOrder318.OpenOrder c :=
  ContactInfinityRegularFractions318.inverseU c ^ (smallIndex i).val.2.val *
    InfinityOverlapLocalization318.toOpen c
      (ContactHOneOrderBases318.infinityBasis c (smallIndex i).val.1)

@[expose] def normalizationPower : Index → ℕ
  | none => 3
  | some _ => 2

theorem t_from_root_zero : t c = root c 0 ^ 2 / algebraMap ℚ (L c) (c 0 : ℚ) := by
  apply (eq_div_iff (constant_ne_zero c (c 0).ne_zero)).mpr
  exact (mul_comm _ _).trans (root_zero_square c).symm

/-- Each of the five concrete overlap representatives has its exact original
character root, original t denominator and original c0 normalization. -/
theorem representative_embedding (i : Index) :
    SourceOpenFractionField318.openEmbedding c (representative c i) =
      CharacterRoot318.root (SourceKummerField318.parameter c) (support i) /
        ((algebraMap ℚ (L c) (c 0 : ℚ)) ^ normalizationPower i * t c) := by
  simp only [representative,map_mul,map_pow,ContactInfinityRegularFractions318.inverse_u_embedding,
    InfinityOverlapLocalization318.toOpen_embedding,ContactHOneOrderBases318.infinity_embedding]
  rw [t_from_root_zero]
  cases i with
  | none =>
    simp only [smallIndex,normalizationPower,support,CharacterRoot318.root,
      Fin.prod_univ_succ,u,ratio,pow_one,pow_zero,mul_one,one_mul]
    change ((algebraMap ℚ (L c) (c 0 : ℚ) / root c 0)⁻¹)^2 *
      (root c 1 / root c 0 * (root c 2 / root c 0) * (root c 3 / root c 0)) = _
    field_simp [root_ne_zero c 0,constant_ne_zero c (c 0).ne_zero] <;> ring
  | some j =>
    fin_cases j <;>
      simp [smallIndex,normalizationPower,support,SourceCharacterFields318.complement_eq,
        SourceTwistArithmetic318.complement,CharacterRoot318.root,u,ratio,
        InfinityFieldCoordinates318.root] <;>
      field_simp [root_ne_zero c 0,constant_ne_zero c (c 0).ne_zero] <;> ring

/-- The rational-valued character is exactly the existing original-field sign. -/
theorem epsilon_field (i : Index) (b : Fin 4 → Bool) :
    algebraMap (RatFunc ℚ) (L c)
      (CharacterRoot318.sign (F:=RatFunc ℚ) (support i) b) =
        algebraMap ℚ (L c) (epsilon i b) := by
  simp only [CharacterRoot318.sign,epsilon,map_prod]
  apply Finset.prod_congr rfl
  intro j _
  cases h : b j <;> simp only [h,Bool.false_eq_true,ite_false,ite_true,map_neg,map_one]

/-- The actual original sign automorphism acts diagonally on each original
overlap representative; no H1 action is assumed in this ring identity. -/
theorem representative_sign (i : Index) (b : Fin 4 → Bool) :
    ContactGlobalSigns318.openEquiv c b (representative c i) =
      algebraMap ℚ (ContactKummerOrder318.OpenOrder c) (epsilon i b) * representative c i := by
  apply SourceOpenFractionField318.openEmbedding_injective c
  rw [SourceSignFieldComparison318.open_embedding,representative_embedding,
    map_mul,RingHom.map_rat_algebraMap,representative_embedding]
  rw [map_div₀,CharacterRoot318.sign_action,epsilon_field]
  simp only [map_mul,map_pow,RingHom.map_rat_algebraMap]
  have ht : FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b (t c) = t c :=
    (FourRootAutomorphisms318.signEquiv (SourceKummerField318.parameter c) b).commutes RatFunc.X
  rw [ht]
  ring

end SourceHOneCharacterRepresentatives318
