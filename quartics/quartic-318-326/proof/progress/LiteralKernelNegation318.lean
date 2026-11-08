module
public import LiteralTriplingNegation318
public import LiteralKernelZeroSection318
public section
noncomputable section
namespace LiteralKernelNegation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "K" => ThreeTorsionTriplingFiber318.fiber A B hD

/-- Actual global negation restricted to the actual tripling zero-fiber. -/
@[expose] def negation : K ⟶ K :=
  pullback.lift
    (pullback.fst (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B) ≫
      GluedNegation318.negation A B)
    (pullback.snd (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B))
    (by rw [Category.assoc,LiteralTriplingNegation318.commute,←Category.assoc,pullback.condition,
      Category.assoc,GluedNegation318.infinity_fixed])
@[reassoc] theorem negation_fst : negation N ≫ pullback.fst _ _=
    pullback.fst (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B) ≫
      GluedNegation318.negation A B := by simp only [negation,pullback.lift_fst]
@[reassoc] theorem negation_snd : negation N ≫ pullback.snd _ _=
    pullback.snd (CompletedIteratedAddition318.tripling A B hD) (WeierstrassGluing318.infinity A B) := by
  simp only [negation,pullback.lift_snd]

theorem negation_twice : negation N ≫ negation N=𝟙 K := by
  apply pullback.hom_ext
  · simp only [Category.assoc,negation_fst,negation_fst_assoc,GluedNegation318.negation_twice,
      Category.comp_id,Category.id_comp]
  · simp only [Category.assoc,negation_snd,Category.id_comp]
@[expose] def iso : K ≅ K where
  hom:=negation N
  inv:=negation N
  hom_inv_id:=negation_twice N
  inv_hom_id:=negation_twice N

/-- The exact original zero-section map is fixed, not just its image. -/
@[reassoc] theorem zero_fixed : LiteralKernelZeroSection318.toKernel N ≫ negation N=
    LiteralKernelZeroSection318.toKernel N := by
  apply pullback.hom_ext
  · simp only [Category.assoc,negation_fst,LiteralKernelZeroSection318.toKernel_fst_assoc,
      LiteralKernelZeroSection318.toKernel_fst,GluedNegation318.infinity_fixed]
  · simp only [Category.assoc,negation_snd]
end LiteralKernelNegation318
