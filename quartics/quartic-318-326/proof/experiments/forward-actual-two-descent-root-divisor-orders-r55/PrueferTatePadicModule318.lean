module
public import PrueferTateResidueBridge318
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.Basis.Basic
public section
noncomputable section
namespace PrueferTatePadicModule318
open ActualTwoDescentDyadicPrueferModel318 PrueferCanonicalTateTower318
open PrueferBoundedCoordinates318 PrueferTateResidueBridge318

/-- Transport along the explicit residue equivalence. The coordinate
formula below verifies that this is the usual finite-residue scalar action,
not merely an unspecified module structure on an isomorphic group. -/
instance padicModule : Module ℤ_[2] (PrimaryTateTower318.tower (Additive PrueferTwo)) :=
  padicEquiv.symm.module ℤ_[2]

def padicLinearEquiv : ℤ_[2] ≃ₗ[ℤ_[2]]
    PrimaryTateTower318.tower (Additive PrueferTwo) :=
  (padicEquiv.symm.linearEquiv ℤ_[2]).symm

theorem padicLinearEquiv_apply (z : ℤ_[2]) : padicLinearEquiv z = padicEquiv z := rfl

theorem smul_padicEquiv (a b : ℤ_[2]) :
    a • padicEquiv b = padicEquiv (a*b) := by
  exact (padicLinearEquiv.map_smul a b).symm

/-- At level n the 2-adic scalar acts by its residue modulo 2^n. -/
theorem smul_coordinate (a : ℤ_[2])
    (x : PrimaryTateTower318.tower (Additive PrueferTwo)) (n : ℕ) :
    (a • x).val n = (PadicInt.toZModPow n a).val • x.val n := by
  obtain ⟨b, rfl⟩ := padicEquiv.surjective x
  rw [smul_padicEquiv]
  apply Subtype.ext
  change encode n (PadicInt.toZModPow n (a*b)).val =
    (PadicInt.toZModPow n a).val • encode n (PadicInt.toZModPow n b).val
  rw [map_mul, ZMod.val_mul, encode_mod]
  rw [mul_nsmul']

/-- A literal singleton basis proves freeness with one generator. -/
def canonicalBasis : Module.Basis Unit ℤ_[2]
    (PrimaryTateTower318.tower (Additive PrueferTwo)) :=
  (Module.Basis.singleton Unit ℤ_[2]).map padicLinearEquiv

theorem canonicalBasis_apply (i : Unit) : canonicalBasis i = canonicalTower := by
  rw [canonicalBasis, Module.Basis.map_apply, Module.Basis.singleton_apply,
    padicLinearEquiv_apply, padicEquiv_one]

/-- Every tower is a unique 2-adic multiple of the distinguished tower. -/
theorem existsUnique_smul_canonical
    (x : PrimaryTateTower318.tower (Additive PrueferTwo)) :
    ∃! a : ℤ_[2], a • canonicalTower = x := by
  have hs (a : ℤ_[2]) : a • canonicalTower = padicEquiv a := by
    rw [← padicEquiv_one, smul_padicEquiv, mul_one]
  refine ⟨padicEquiv.symm x, ?_, ?_⟩
  · rw [hs, padicEquiv.apply_symm_apply]
  · intro a ha
    apply padicEquiv.injective
    rw [← hs, ha, padicEquiv.apply_symm_apply]

end PrueferTatePadicModule318
