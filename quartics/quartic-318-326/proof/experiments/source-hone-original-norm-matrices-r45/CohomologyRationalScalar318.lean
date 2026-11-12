module
public import StructureRationalScalar318
public import SheafInverseImageConstants318
public import SheafCohomologyRetraction318
public import Mathlib.Algebra.Module.Rat

public section
noncomputable section
namespace CohomologyRationalScalar318
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open StructureAdditiveSheaf318 SheafInverseImageConstants318 SheafCohomologyRetraction318
set_option maxHeartbeats 700000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {X : TopCat.{0}}

/-- A genuine rational action on the coefficient sheaf induces its action on actual Ext cohomology. -/
@[expose,reducible] def ofAction (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (a : ℚ → (F ⟶ F)) (hzero : a 0 = 0) (hone : a 1 = 𝟙 F)
    (hadd : ∀ r s, a (r+s) = a r+a s) (hmul : ∀ r s, a (r*s) = a s ≫ a r)
    (n : ℕ) : Module ℚ (Sheaf.H F n) where
  smul r x := Sheaf.H.map (a r) n x
  one_smul x := by
    change Sheaf.H.map (a 1) n x = x
    rw [hone,Sheaf.H.map_id_apply]
  mul_smul r s x := by
    change Sheaf.H.map (a (r*s)) n x = Sheaf.H.map (a r) n (Sheaf.H.map (a s) n x)
    rw [hmul,Sheaf.H.map_comp_apply]
  smul_zero r := map_zero _
  smul_add r x y := map_add _ _ _
  add_smul r s x := by
    change Sheaf.H.map (a (r+s)) n x = Sheaf.H.map (a r) n x + Sheaf.H.map (a s) n x
    rw [hadd,Sheaf.H.map_add_apply]
  zero_smul x := by
    change Sheaf.H.map (a 0) n x = 0
    rw [hzero,Sheaf.H.map_apply,Ext.mk₀_zero,Ext.comp_zero]

variable {S : Scheme.{0}} (p : S ⟶ Spec (CommRingCat.of ℚ))

/-- The structural Q-module on the unchanged actual scheme-cohomology group. -/
@[expose,reducible] def structureModule (n : ℕ) : Module ℚ (structureH S n) :=
  ofAction (sheaf S) (StructureRationalScalar318.multiply p)
    (StructureRationalScalar318.multiply_zero p) (StructureRationalScalar318.multiply_one p)
    (StructureRationalScalar318.multiply_add p) (StructureRationalScalar318.multiply_mul p) n

theorem structure_smul (n : ℕ) (a : ℚ) (x : structureH S n) :
    letI := structureModule p n
    a • x = Sheaf.H.map (StructureRationalScalar318.multiply p a) n x := rfl

/-- Direct-image coefficients carry the same original rational multiplication before cohomology. -/
@[expose,reducible] def pushedModule {T : Scheme.{0}} (f : S ⟶ T) (n : ℕ) : Module ℚ (pushedH f n) :=
  ofAction (pushed f) (fun a => (directImage f.base).map (StructureRationalScalar318.multiply p a))
    (by rw [StructureRationalScalar318.multiply_zero]; exact (directImage f.base).map_zero _ _)
    (by rw [StructureRationalScalar318.multiply_one]; exact (directImage f.base).map_id _)
    (by intro r s; rw [StructureRationalScalar318.multiply_add]; exact (directImage f.base).map_add)
    (by intro r s; rw [StructureRationalScalar318.multiply_mul]; exact (directImage f.base).map_comp _ _) n

theorem pushed_smul {T : Scheme.{0}} (f : S ⟶ T) (n : ℕ) (a : ℚ) (x : pushedH f n) :
    letI := pushedModule p f n
    a • x = Sheaf.H.map ((directImage f.base).map (StructureRationalScalar318.multiply p a)) n x := rfl

/-- The structural action is confirmed against the original global-section comparison in degree zero. -/
theorem structure_HZero_smul (a : ℚ) (x : structureH S 0) :
    letI := structureModule p 0
    structureHZero S (a • x) = NormalizedStructureTrace318.scalar p ⊤ a * structureHZero S x := by
  exact (Sheaf.H.equiv₀_naturality CategoryTheory.Limits.isTerminalTop
    (StructureRationalScalar318.multiply p a) x).symm

end CohomologyRationalScalar318
