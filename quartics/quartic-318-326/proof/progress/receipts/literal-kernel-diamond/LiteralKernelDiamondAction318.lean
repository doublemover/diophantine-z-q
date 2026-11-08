module
public import LiteralKernelDiamond318
public section
noncomputable section
namespace LiteralKernelDiamondAction318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits ThreeTorsionLabels318
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N:ℕ)
local notation "A" => OpenJAffineScheme318.A N
local notation "B" => OpenJAffineScheme318.B N
local notation "hD" => OpenJAffineScheme318.discriminant_unit N
local notation "K" => ThreeTorsionTriplingFiber318.fiber A B hD

/-- Actual diamond automorphisms of the actual global tripling fiber. -/
@[expose] def diamond (g:(ZMod 3)ˣ) : K ≅ K :=
  if g=1 then Iso.refl K else LiteralKernelNegation318.iso N
@[simp] theorem diamond_one : diamond N 1=Iso.refl K := by simp [diamond]
@[simp] theorem diamond_neg_one : diamond N (-1)=LiteralKernelNegation318.iso N := by
  simp [diamond,neg_one_ne_one]

theorem diamond_mul (g h:(ZMod 3)ˣ) : diamond N (g*h)=diamond N g ≪≫ diamond N h := by
  rcases unit_cases g with rfl|rfl <;> rcases unit_cases h with rfl|rfl
  · simp
  · simp
  · simp
  · apply Iso.ext
    simp only [show (-1:(ZMod 3)ˣ)*(-1)=1 by decide,diamond_one,diamond_neg_one,
      Iso.refl_hom,Iso.trans_hom,LiteralKernelNegation318.iso]
    exact (LiteralKernelNegation318.negation_twice N).symm

@[reassoc] theorem zero_fixed (g:(ZMod 3)ˣ) :
    LiteralKernelZeroSection318.toKernel N ≫ (diamond N g).hom=LiteralKernelZeroSection318.toKernel N := by
  rcases unit_cases g with rfl|rfl
  · simp only [diamond_one,Iso.refl_hom,Category.comp_id]
  · exact LiteralKernelNegation318.zero_fixed N

variable [Nontrivial (OpenJModel318.Base N)]
/-- Compatibility with every unit in the original published rank-eight
diamond action; its original nontrivial-base premise is retained. -/
@[reassoc] theorem published_compatibility (g:(ZMod 3)ˣ) :
    Spec.map (CommRingCat.ofHom (ThreeTorsionDiamond318.diamond A B hD g).toAlgHom.toRingHom) ≫
      ThreeTorsionTriplingFiber318.toFiber A B hD=
    ThreeTorsionTriplingFiber318.toFiber A B hD ≫ (diamond N g).hom := by
  rcases unit_cases g with rfl|rfl
  · simp only [ThreeTorsionDiamond318.diamond_one,diamond_one,Iso.refl_hom,Category.comp_id]
    change Spec.map (𝟙 _) ≫ _=_
    rw [Spec.map_id,Category.id_comp]
  · exact LiteralKernelDiamond318.published_minus_one N

/-- The exact whole-kernel decomposition respects the whole existing diamond
action, with the actual zero component fixed. -/
theorem coproduct_equivariance (g:(ZMod 3)ˣ) :
    (diamond N g).hom ≫ (LiteralFullKernel318.iso N).hom=
      (LiteralFullKernel318.iso N).hom ≫ coprod.map
        (Spec.map (CommRingCat.ofHom (ThreeTorsionDiamond318.diamond A B hD g).toAlgHom.toRingHom)) (𝟙 _) := by
  rcases unit_cases g with rfl|rfl
  · simp only [diamond_one,Iso.refl_hom,Category.id_comp,ThreeTorsionDiamond318.diamond_one]
    change _=_ ≫ coprod.map (Spec.map (𝟙 _)) (𝟙 _)
    rw [Spec.map_id,coprod.map_id_id,Category.comp_id]
  · rw [diamond_neg_one,ThreeTorsionDiamond318.diamond_neg_one]
    exact LiteralKernelDiamond318.coproduct_equivariance N
end LiteralKernelDiamondAction318
