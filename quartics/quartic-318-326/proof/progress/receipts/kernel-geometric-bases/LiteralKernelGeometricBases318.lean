module
public import LiteralKernelFieldCard318
public import F3RankTwoBases318
public section
noncomputable section
namespace LiteralKernelGeometricBases318
open AlgebraicGeometry CategoryTheory
variable (N : ℕ) (F : Type) [Field F] [IsAlgClosed F]
  [Algebra (OpenJModel318.Base N) F] [NeZero N]
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base N) F))
local notation "V" => LiteralKernelSchemePoints318.Points N b
/-- Dimension of the genuine geometric kernel point module, not arbitrary splitting labels. -/
theorem finrank_two : Module.finrank (ZMod 3) V = 2 :=
  F3NineDimension318.finrank_two V (LiteralKernelFieldCard318.card_nine N F)
/-- Actual independent points are exactly ordered F3 bases of the geometric kernel. -/
def pairBasisEquiv : F3RankTwoBases318.Pairs V ≃ Module.Basis (Fin 2) (ZMod 3) V :=
  F3RankTwoBases318.pairBasisEquiv V (finrank_two N F)
@[simp] theorem first_vector (p : F3RankTwoBases318.Pairs V) :
    pairBasisEquiv N F p 0 = p.val.1 := F3RankTwoBases318.pairBasis_zero V _ p
@[simp] theorem second_vector (p : F3RankTwoBases318.Pairs V) :
    pairBasisEquiv N F p 1 = p.val.2 := F3RankTwoBases318.pairBasis_one V _ p

theorem card_pairs : Nat.card (F3RankTwoBases318.Pairs V) = 48 :=
  F3RankTwoBases318.card_pairs V (LiteralKernelFieldCard318.card_nine N F)
theorem card_bases : Nat.card (Module.Basis (Fin 2) (ZMod 3) V) = 48 :=
  F3RankTwoBases318.card_bases V (LiteralKernelFieldCard318.card_nine N F)
end LiteralKernelGeometricBases318
