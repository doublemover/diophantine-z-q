module
public import TwoTorsionCurve318
public import TwoTorsionPoints318
public section
noncomputable section
namespace LiteralTwoTorsion318
open Polynomial CategoryTheory AlgebraicGeometry
open scoped TensorProduct
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
open OpenJModel318 OpenJAffineScheme318

lemma denominator_ne_zero (N:ℕ) (hN:N≠0) : OpenJModel318.denominator N≠0 := by
  unfold OpenJModel318.denominator
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hN)
    · exact Polynomial.X_ne_zero
  · simpa using (Polynomial.X_sub_C_ne_zero (1728:ℤ))

instance base_domain (N:ℕ) [NeZero N] : IsDomain (Base N) :=
  IsLocalization.Away.isDomain _ (denominator_ne_zero N (NeZero.ne N))

abbrev Ring (N:ℕ) := ShortTwoTorsion318.Ring (A N) (B N)
instance finite (N:ℕ) : Module.Finite (Base N) (Ring N) :=
  ShortTwoTorsion318.finite _ _
instance etale (N:ℕ) : Algebra.Etale (Base N) (Ring N) :=
  ShortTwoTorsion318.etale _ _ (discriminant_unit N)
instance faithfullyFlat (N:ℕ) [NeZero N] : Module.FaithfullyFlat (Base N) (Ring N) :=
  ShortTwoTorsion318.faithfullyFlat _ _

theorem rank_three (N:ℕ) [NeZero N] : Module.finrank (Base N) (Ring N)=3 :=
  ShortTwoTorsion318.rank_three _ _

/-- An actual nonzero-two-torsion cubic over the literal integral j-family,
with no finite-etale algebra existence hypothesis. N is the base localization
level here; this does not assert a primitive N-torsion construction. -/
theorem actual_cover (N:ℕ) [NeZero N] :
    IsFinite (TwoTorsionCurve318.structureMap (A N) (B N)) ∧
    Etale (TwoTorsionCurve318.structureMap (A N) (B N)) ∧
    Flat (TwoTorsionCurve318.structureMap (A N) (B N)) ∧
    Surjective (TwoTorsionCurve318.structureMap (A N) (B N)) := by
  obtain ⟨hf,he⟩:=TwoTorsionCurve318.finite_etale (A N) (B N) (discriminant_unit N)
  exact ⟨hf,he,TwoTorsionCurve318.flat_surjective (A N) (B N)⟩

@[expose] def splitting (N:ℕ) [NeZero N] :=
  ShortTwoTorsion318.splitting (A N) (B N) (discriminant_unit N)

/-- Evaluation in a constructed finite-etale faithfully-flat ring splits the
actual cubic coordinate algebra; a splitting ring is not supplied. -/
@[expose] def splitEquiv (N:ℕ) [NeZero N] :
    (splitting N).S⊗[Base N]Ring N≃ₐ[(splitting N).S]
      (Fin (ShortTwoTorsion318.polynomial (A N) (B N)).natDegree→(splitting N).S) :=
  MonicEtaleSplitting318.canonicalSplitEquiv _ (ShortTwoTorsion318.monic _ _)
    (ShortTwoTorsion318.separable _ _ (discriminant_unit N))

end LiteralTwoTorsion318
