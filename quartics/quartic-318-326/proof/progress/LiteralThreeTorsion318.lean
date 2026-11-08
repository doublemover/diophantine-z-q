module
public import ThreeTorsionScheme318
public import LiteralTwoTorsion318
public section
noncomputable section
namespace LiteralThreeTorsion318
open OpenJModel318 OpenJAffineScheme318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0

instance inverse_three (N:ℕ) : Invertible (3:Base N) := (base_units N).2.1.invertible
abbrev Ring (N:ℕ) := ThreeTorsionAlgebra318.Ring (A N) (B N) (discriminant_unit N)

instance finite (N:ℕ) : Module.Finite (Base N) (Ring N) :=
  ThreeTorsionAlgebra318.finite _ _ _
instance free (N:ℕ) : Module.Free (Base N) (Ring N) :=
  ThreeTorsionAlgebra318.free _ _ _
instance etale (N:ℕ) : Algebra.Etale (Base N) (Ring N) :=
  ThreeTorsionAlgebra318.etale _ _ _
instance faithfullyFlat (N:ℕ) [NeZero N] : Module.FaithfullyFlat (Base N) (Ring N) :=
  ThreeTorsionAlgebra318.faithfullyFlat _ _ _

theorem rank_eight (N:ℕ) [NeZero N] : Module.finrank (Base N) (Ring N)=8 :=
  ThreeTorsionAlgebra318.rank_eight _ _ _

/-- The explicit literal nonzero-three-torsion equations give a rank-eight
finite-etale faithfully-flat family over the actual integral open-j ring.
Here N is the base localization level; the torsion order is always three. -/
theorem actual_cover (N:ℕ) [NeZero N] :
    IsFinite (ThreeTorsionScheme318.structureMap (A N) (B N) (discriminant_unit N)) ∧
    Etale (ThreeTorsionScheme318.structureMap (A N) (B N) (discriminant_unit N)) ∧
    Flat (ThreeTorsionScheme318.structureMap (A N) (B N) (discriminant_unit N)) ∧
    Surjective (ThreeTorsionScheme318.structureMap (A N) (B N) (discriminant_unit N)) := by
  obtain ⟨hf,he⟩:=ThreeTorsionScheme318.finite_etale (A N) (B N) (discriminant_unit N)
  exact ⟨hf,he,ThreeTorsionScheme318.flat_surjective (A N) (B N) (discriminant_unit N)⟩

end LiteralThreeTorsion318
