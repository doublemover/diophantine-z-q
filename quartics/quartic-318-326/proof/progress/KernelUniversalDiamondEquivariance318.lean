module
public import KernelUniversalDiamond318
public section
noncomputable section
namespace KernelUniversalDiamondEquivariance318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open KernelUniversalFrame318
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
variable (N : ℕ)
local notation "C" => ∐ fun _ : Fin 2 → ZMod 3 => Frame N
/-- Actual coefficient permutation of the original coproduct, with identity on each frame copy. -/
@[expose] def coefficientMap (g : (ZMod 3)ˣ) : C ⟶ C :=
  Sigma.desc (fun c => Sigma.ι (fun _ : Fin 2 → ZMod 3 => Frame N) ((g : ZMod 3) • c))
@[reassoc] theorem component (g : (ZMod 3)ˣ) (c : Fin 2 → ZMod 3) :
    Sigma.ι (fun _ : Fin 2 → ZMod 3 => Frame N) c ≫ coefficientMap N g =
      Sigma.ι (fun _ : Fin 2 → ZMod 3 => Frame N) ((g : ZMod 3) • c) := Sigma.ι_comp_desc _ _
@[simp] theorem coefficient_one : coefficientMap N 1 = 𝟙 C := by
  apply Sigma.hom_ext
  intro c
  simp only [component,Units.val_one,one_smul,Category.comp_id]
@[reassoc] theorem coefficient_mul (g h : (ZMod 3)ˣ) :
    coefficientMap N g ≫ coefficientMap N h = coefficientMap N (g*h) := by
  apply Sigma.hom_ext
  intro c
  simp only [component_assoc,component,Units.val_mul,smul_smul]
  rw [mul_comm (h : ZMod 3) (g : ZMod 3)]
@[expose] def coefficientIso (g : (ZMod 3)ˣ) : C ≅ C where
  hom := coefficientMap N g
  inv := coefficientMap N g⁻¹
  hom_inv_id := by rw [coefficient_mul,mul_inv_cancel,coefficient_one]
  inv_hom_id := by rw [coefficient_mul,inv_mul_cancel,coefficient_one]

variable [NeZero N]
/-- Exact equivariance of the actual universal full-kernel Scheme isomorphism
with the original global diamond and its genuine F3 coefficient action. -/
theorem equivariance (g : (ZMod 3)ˣ) :
    (KernelUniversalTrivialization318.iso N).hom ≫ KernelUniversalDiamond318.map N g =
      coefficientMap N g ≫ (KernelUniversalTrivialization318.iso N).hom := by
  apply Sigma.hom_ext
  intro c
  rw [KernelUniversalTrivialization318.component_assoc,KernelUniversalDiamond318.section_map,
    component_assoc,KernelUniversalTrivialization318.component]
/-- In particular, the original elliptic negation is exactly c ↦ -c in the proved additive trivialization. -/
theorem negation_equivariance :
    (KernelUniversalTrivialization318.iso N).hom ≫ KernelUniversalDiamond318.map N (-1) =
      coefficientMap N (-1) ≫ (KernelUniversalTrivialization318.iso N).hom := equivariance N (-1)
end KernelUniversalDiamondEquivariance318
