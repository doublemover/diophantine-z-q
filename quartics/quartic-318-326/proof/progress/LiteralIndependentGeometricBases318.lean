module
public import IndependentPairSingleton318
public import LiteralKernelGeometricBases318
public section
noncomputable section
namespace LiteralIndependentGeometricBases318
open AlgebraicGeometry CategoryTheory
variable (N : ℕ) (F : Type) [Field F] [IsAlgClosed F]
  [Algebra (OpenJModel318.Base N) F] [NeZero N]
local notation "b" => Spec.map (CommRingCat.ofHom (algebraMap (OpenJModel318.Base N) F))
local notation "V" => LiteralKernelSchemePoints318.Points N b
/-- The already represented open's actual geometric sections, not a new abstract 48-element type. -/
abbrev Sections := IndependentPairSingleton318.Sections N b
@[expose] def basisEquiv : Sections N F ≃ Module.Basis (Fin 2) (ZMod 3) V :=
  (IndependentPairSingleton318.equivalence N b (IsLocalRing.closedPoint F)).trans
    (LiteralKernelGeometricBases318.pairBasisEquiv N F)
/-- The two universal kernel projections are exactly the two basis vectors. -/
@[simp] theorem first_value (s : Sections N F) :
    ((basisEquiv N F s) 0).val = s.val ≫ LiteralIndependentPairFunctor318.first N := by
  change ((LiteralKernelGeometricBases318.pairBasisEquiv N F _ ) 0).val = _
  rw [LiteralKernelGeometricBases318.first_vector]
  exact IndependentPairSingleton318.first_value N b _ s
@[simp] theorem second_value (s : Sections N F) :
    ((basisEquiv N F s) 1).val = s.val ≫ LiteralIndependentPairFunctor318.second N := by
  change ((LiteralKernelGeometricBases318.pairBasisEquiv N F _ ) 1).val = _
  rw [LiteralKernelGeometricBases318.second_vector]
  exact IndependentPairSingleton318.second_value N b _ s
/-- Exactly 48 geometric sections of the actual finite-etale independent-pair Scheme. -/
theorem card_forty_eight : Nat.card (Sections N F) = 48 := by
  rw [Nat.card_congr (basisEquiv N F)]
  exact LiteralKernelGeometricBases318.card_bases N F
end LiteralIndependentGeometricBases318
