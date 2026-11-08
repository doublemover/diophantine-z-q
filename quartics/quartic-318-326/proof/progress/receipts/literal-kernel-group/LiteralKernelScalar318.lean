module
public import LiteralKernelSchemePoints318
public import LiteralKernelDiamondAction318
public import Mathlib.Algebra.Module.ZMod
public section
noncomputable section
namespace LiteralKernelScalar318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LiteralKernelSchemePoints318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ) {T:Scheme}
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
variable (b:T ⟶ Spec (CommRingCat.of (OpenJModel318.Base N)))

theorem three_zero (p:Points N b) : (3:ℕ) • p=0 := by
  apply embedding_injective N b
  rw [map_nsmul,map_zero]
  exact (toKilled N b p).property
/-- Canonical F3 scalar structure on actual kernel-valued Scheme points,
induced by the actual represented addition, not by splitting labels. -/
instance module : Module (ZMod 3) (Points N b):=AddCommGroup.zmodModule (three_zero N b)

theorem zero_val : (0:Points N b).val=b ≫ LiteralKernelZeroSection318.toKernel N := by
  apply pullback.hom_ext
  · have h:=congrArg Subtype.val ((embedding N b).map_zero)
    change (0:Points N b).val ≫ inclusion N=b ≫ WeierstrassGluing318.infinity A B at h
    simpa only [Category.assoc,LiteralKernelZeroSection318.toKernel_fst,inclusion] using h
  · simp only [Category.assoc,LiteralKernelZeroSection318.toKernel_snd,Category.comp_id]
    exact (0:Points N b).property

theorem neg_val (p:Points N b) : (-p).val=p.val ≫ LiteralKernelNegation318.negation N := by
  apply pullback.hom_ext
  · have h:=congrArg Subtype.val (map_neg (embedding N b) p)
    change (-p).val ≫ inclusion N=(p.val ≫ inclusion N) ≫ GluedNegation318.negation A B at h
    simpa only [inclusion,Category.assoc,LiteralKernelNegation318.negation_fst] using h
  · simp only [Category.assoc,LiteralKernelNegation318.negation_snd]
    exact (-p).property.trans p.property.symm

theorem add_inclusion (p q:Points N b) : (p+q).val ≫ inclusion N=
    LiteralSchemePointOperations318.pair N b (intoCurve N b p) (intoCurve N b q) ≫
      CompletedAddition318.addition A B hD :=
  congrArg Subtype.val ((embedding N b).map_add p q)

/-- The already constructed global diamond involution is precisely scalar
minus one on the actual kernel group functor. -/
theorem minus_one_val (p:Points N b) : ((-1:ZMod 3) • p).val=p.val ≫ LiteralKernelNegation318.negation N := by
  rw [neg_one_smul]
  exact neg_val N b p

/-- Every original unit diamond acts by its genuine F3 scalar on the entire
kernel; no arbitrary choice of eight labels is used. -/
theorem diamond_val (g:(ZMod 3)ˣ) (p:Points N b) :
    ((g:ZMod 3) • p).val=p.val ≫ (LiteralKernelDiamondAction318.diamond N g).hom := by
  rcases ThreeTorsionLabels318.unit_cases g with rfl|rfl
  · simp only [Units.val_one,one_smul,LiteralKernelDiamondAction318.diamond_one,Iso.refl_hom,Category.comp_id]
  · simpa only [Units.val_neg,Units.val_one,LiteralKernelDiamondAction318.diamond_neg_one,LiteralKernelNegation318.iso]
      using minus_one_val N b p
end LiteralKernelScalar318
