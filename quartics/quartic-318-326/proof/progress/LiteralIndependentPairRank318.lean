module
public import FiniteEtaleRankFromSections318
public import LiteralIndependentGeometricBases318
public section
noncomputable section
namespace LiteralIndependentPairRank318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N : ℕ) [NeZero N]
local notation "p" => LiteralIndependentPairFinite318.structureMap N
local instance : IsFinite p := (LiteralIndependentPairFinite318.finite_etale N).1
local instance : Etale p := (LiteralIndependentPairFinite318.finite_etale N).2
/-- The actual finite-etale independent-pair Scheme has structural rank 48 everywhere. -/
theorem rank_forty_eight (x : Spec (CommRingCat.of (OpenJModel318.Base N))) : (p).finrank x = 48 := by
  apply FiniteEtaleRankFromSections318.rank_eq p 48
  intro F _ _ b
  obtain ⟨φ,rfl⟩ := Spec.map_surjective b
  letI : Algebra (OpenJModel318.Base N) F := φ.hom.toAlgebra
  exact LiteralIndependentGeometricBases318.card_forty_eight N F
/-- The original independent-pair cover is genuinely surjective, not merely nonempty over one fiber. -/
theorem surjective : Surjective p := by
  apply (Scheme.Hom.one_le_finrank_iff_surjective p).mp
  intro x
  rw [rank_forty_eight]
  change 1 ≤ (48 : ℕ)
  decide

theorem finite_etale_surjective : IsFinite p ∧ Etale p ∧ Surjective p :=
  ⟨inferInstance,inferInstance,surjective N⟩
end LiteralIndependentPairRank318
