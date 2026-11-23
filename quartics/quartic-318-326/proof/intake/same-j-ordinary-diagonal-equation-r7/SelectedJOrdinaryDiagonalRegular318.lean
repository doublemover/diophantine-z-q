module
public import SelectedJAbsoluteStructuralKernel318
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.PolynomialAlgebra
public import Mathlib.RingTheory.RingHom.Flat

public section
noncomputable section

open Algebra Polynomial
open scoped TensorProduct
open SelectedJAbsoluteStructuralKernel318

namespace SelectedJOrdinaryDiagonalRegular318

private theorem flat_map_regular {S T : Type*} [CommRing S] [CommRing T]
    (f : S →+* T) (hf : f.Flat) {s : S} (hs : IsRegular s) : IsRegular (f s) := by
  let : Algebra S T := f.toAlgebra
  let : Module.Flat S T := hf
  exact isLeftRegular_iff_isRegular.mp
    (IsSMulRegular.of_flat (S := T) hs.left.isSMulRegular).isLeftRegular

/-- On any flat algebra over this literal ordinary j-line the full structural
diagonal equation is a nonzerodivisor, including when the product has zero
divisors. It is the flat image of the monic polynomial X−j after interchanging
the two factors to match our first-coordinate sign convention. -/
theorem deltaJ_regular (N : ℕ) (B : Type*) [CommRing B] [Algebra (A N) B]
    [Module.Flat (A N) B] : IsRegular (deltaJ N B) := by
  let j := algebraMap (A N) B (OpenJModel318.jCoord N)
  let f := ((algebraMap (A N) B).comp (algebraMap ℤ[X] (A N))).toIntAlgHom
  have hf : f.toRingHom.Flat := RingHom.Flat.comp
    (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (A N)
      (Submonoid.powers (OpenJModel318.denominator N))))
    (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat (A N) B))
  let e := polyEquivTensor ℤ B
  let t := Algebra.TensorProduct.lTensor (S := ℤ) B f
  let c := Algebra.TensorProduct.comm ℤ B B
  let F := c.toRingHom.comp (t.toRingHom.comp e.toRingHom)
  have ht : t.toRingHom.Flat := hf.lTensor B
  have hF : F.Flat := RingHom.Flat.comp
    (RingHom.Flat.comp (RingHom.Flat.of_bijective e.bijective) ht)
    (RingHom.Flat.of_bijective c.bijective)
  have hfx : f (X : ℤ[X]) = j := rfl
  let d : B ⊗[ℤ] B := j ⊗ₜ[ℤ] (1:B) - (1:B) ⊗ₜ[ℤ] j
  have hcomp (z : B[X]) : F z = c (t (e z)) := rfl
  have eX : e (X : B[X]) = (1:B) ⊗ₜ[ℤ] (X : ℤ[X]) :=
    (polyEquivTensor_apply ℤ B _).trans (eval₂_X _ _)
  have eC : e (C j) = j ⊗ₜ[ℤ] (1 : ℤ[X]) := by
    let l : B →ₐ[ℤ] B ⊗[ℤ] ℤ[X] := Algebra.TensorProduct.includeLeft
    calc
      e (C j) = (C j).eval₂ (l : B →+* B ⊗[ℤ] ℤ[X]) ((1:B) ⊗ₜ[ℤ] (X : ℤ[X])) :=
        polyEquivTensor_apply ℤ B _
      _ = (l : B →+* B ⊗[ℤ] ℤ[X]) j := eval₂_C _ _
      _ = l j := congrFun (AlgHom.coe_toRingHom l) j
      _ = _ := Algebra.TensorProduct.includeLeft_apply j
  have tmap (b : B) (p : ℤ[X]) : t (b ⊗ₜ[ℤ] p) = b ⊗ₜ[ℤ] f p :=
    Algebra.TensorProduct.map_tmul (AlgHom.id ℤ B) f b p
  have hx : F (X - C j) = d := by
    simp only [hcomp, map_sub, eX, eC, tmap, hfx, map_one, c, Algebra.TensorProduct.comm_tmul, d]
  have hd : IsRegular d := hx ▸ flat_map_regular F hF (monic_X_sub_C j).isRegular
  have hz : d ∈ RingHom.ker (structural N B).toRingHom := by
    change structural N B (j ⊗ₜ[ℤ] (1:B) - (1:B) ⊗ₜ[ℤ] j) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    exact RingHom.congr_fun (Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (R := A N) (A := B) (B := B)) (OpenJModel318.jCoord N)
  rw [structural_kernel] at hz
  obtain ⟨u,hu⟩ := Ideal.mem_span_singleton.mp hz
  rw [hu] at hd
  exact (isRegular_mul_iff.mp hd).1

end SelectedJOrdinaryDiagonalRegular318
#print axioms SelectedJOrdinaryDiagonalRegular318.deltaJ_regular
