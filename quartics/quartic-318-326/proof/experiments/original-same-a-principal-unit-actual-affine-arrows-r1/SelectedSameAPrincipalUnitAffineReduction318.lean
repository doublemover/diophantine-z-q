module
public import Mathlib.Algebra.TrivSqZeroExt.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

public section
noncomputable section
open CategoryTheory

namespace SelectedSameAPrincipalUnitAffineReduction318
universe u
variable (B : Type u) [CommRing B]
abbrev dual := TrivSqZeroExt B B
abbrev inclusion : B →ₗ[B] dual B := TrivSqZeroExt.inrHom B B
abbrev projection : dual B →ₗ[B] B := (TrivSqZeroExt.fstHom B B B).toLinearMap
abbrev retraction : dual B →ₗ[B] B := TrivSqZeroExt.sndHom B B
abbrev sectionMap : B →ₗ[B] dual B := (TrivSqZeroExt.inlAlgHom B B B).toLinearMap

@[expose] def row : ShortComplex (ModuleCat.{u} B) :=
  ShortComplex.mk (ModuleCat.ofHom (inclusion B)) (ModuleCat.ofHom (projection B)) (by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact TrivSqZeroExt.fst_inr B b)

@[expose] def splitting : (row B).Splitting where
  r := ModuleCat.ofHom (retraction B)
  s := ModuleCat.ofHom (sectionMap B)
  f_r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact TrivSqZeroExt.snd_inr B b
  s_g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro b
    exact TrivSqZeroExt.fst_inl B b
  id := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    change TrivSqZeroExt.inr z.snd + TrivSqZeroExt.inl z.fst = z
    rw [add_comm]
    exact TrivSqZeroExt.inl_fst_add_inr_snd_eq z

theorem shortExact : (row B).ShortExact := (splitting B).shortExact

theorem epsilon_mul_lift (b : B) :
    (TrivSqZeroExt.inr 1 : dual B) * TrivSqZeroExt.inl b = inclusion B b := by
  change (TrivSqZeroExt.inr 1 : dual B) * TrivSqZeroExt.inl b = TrivSqZeroExt.inr b
  rw [mul_comm, TrivSqZeroExt.inl_mul_inr, smul_eq_mul, mul_one]

theorem normalized_frame_coordinates (p : B) (z : dual B) :
    let t := (1 + TrivSqZeroExt.inr p : dual B) * z
    t.fst = z.fst ∧ t.snd = z.snd + p * z.fst := by
  dsimp only
  rw [add_mul, one_mul]
  constructor
  · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_mul,
      TrivSqZeroExt.fst_inr, zero_mul, add_zero]
  · rw [mul_comm (TrivSqZeroExt.inr p : dual B)]
    simp [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_mul,
      TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr, smul_eq_mul, mul_comm]

end SelectedSameAPrincipalUnitAffineReduction318
