module
public import KernelUniversalTrivialization318
public import LiteralKernelDiamondAction318
public section
noncomputable section
namespace KernelUniversalDiamond318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KernelUniversalFrame318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N : ℕ)
@[reassoc] theorem diamond_base (g : (ZMod 3)ˣ) :
    (LiteralKernelDiamondAction318.diamond N g).hom ≫ LiteralKernelSchemePoints318.structureMap N =
      LiteralKernelSchemePoints318.structureMap N := by
  rcases ThreeTorsionLabels318.unit_cases g with rfl | rfl
  · simp only [LiteralKernelDiamondAction318.diamond_one,Iso.refl_hom,Category.id_comp]
  · exact LiteralKernelNegation318.negation_snd N
/-- Actual base change of the original global diamond, retaining the original kernel projection. -/
@[expose] def map (g : (ZMod 3)ˣ) : family N ⟶ family N :=
  pullback.lift (original N ≫ (LiteralKernelDiamondAction318.diamond N g).hom)
    (projection N) (by rw [Category.assoc,diamond_base];exact pullback.condition)
@[reassoc] theorem map_original (g : (ZMod 3)ˣ) : map N g ≫ original N =
    original N ≫ (LiteralKernelDiamondAction318.diamond N g).hom := pullback.lift_fst _ _ _
@[reassoc] theorem map_projection (g : (ZMod 3)ˣ) : map N g ≫ projection N = projection N :=
  pullback.lift_snd _ _ _
@[simp] theorem map_one : map N 1 = 𝟙 (family N) := by
  apply pullback.hom_ext
  · change map N 1 ≫ original N = (𝟙 (family N)) ≫ original N
    simp only [map_original,LiteralKernelDiamondAction318.diamond_one,Iso.refl_hom,Category.id_comp]
    exact Category.comp_id (original N)
  · change map N 1 ≫ projection N = (𝟙 (family N)) ≫ projection N
    simp only [map_projection,Category.id_comp]
@[reassoc] theorem map_mul (g h : (ZMod 3)ˣ) : map N g ≫ map N h = map N (g*h) := by
  apply pullback.hom_ext
  · change (map N g ≫ map N h) ≫ original N = map N (g*h) ≫ original N
    simp only [Category.assoc,map_original,map_original_assoc,LiteralKernelDiamondAction318.diamond_mul,Iso.trans_hom]
  · change (map N g ≫ map N h) ≫ projection N = map N (g*h) ≫ projection N
    simp only [Category.assoc,map_projection]
@[expose] def iso (g : (ZMod 3)ˣ) : family N ≅ family N where
  hom := map N g
  inv := map N g⁻¹
  hom_inv_id := by rw [map_mul,mul_inv_cancel,map_one]
  inv_hom_id := by rw [map_mul,inv_mul_cancel,map_one]

/-- The genuine additive coefficients, rather than arbitrary labels, are multiplied by the unit. -/
theorem combination_smul (a : ZMod 3) (c : Fin 2 → ZMod 3) :
    combination N (a • c) = a • combination N c := by
  simp only [combination,Pi.smul_apply,smul_eq_mul,smul_add,smul_smul]
@[reassoc] theorem section_map (g : (ZMod 3)ˣ) (c : Fin 2 → ZMod 3) :
    sectionMap N c ≫ map N g = sectionMap N ((g : ZMod 3) • c) := by
  apply pullback.hom_ext
  · change (sectionMap N c ≫ map N g) ≫ original N = _ ≫ original N
    rw [Category.assoc,map_original,←Category.assoc,section_original,section_original,combination_smul]
    exact (LiteralKernelScalar318.diamond_val N (frameBase N) g (combination N c)).symm
  · change (sectionMap N c ≫ map N g) ≫ projection N = _ ≫ projection N
    rw [Category.assoc,map_projection,section_projection,section_projection]
end KernelUniversalDiamond318
