module
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Div
public section
noncomputable section
namespace SymmetricPrimitiveRegular318
open Polynomial
universe u v
variable (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
  (φ : M →ₗ[R] R)
local notation "A" => SymmetricAlgebra R M

/-- Translation in a new polynomial direction. A split primitive vector
becomes a monic linear polynomial, even over rings with zero divisors. -/
@[expose] def generator : M →ₗ[R] Polynomial A :=
  (Polynomial.CAlgHom : A →ₐ[R] Polynomial A).toLinearMap.comp (SymmetricAlgebra.ι R M) +
    φ.smulRight (Polynomial.X : Polynomial A)
@[expose] def translate : A →ₐ[R] Polynomial A := SymmetricAlgebra.lift (generator R M φ)
@[expose] def atZero : Polynomial A →ₐ[R] A :=
  Polynomial.aevalTower (AlgHom.id R A) (0 : A)

lemma translate_generator (x : M) :
    translate R M φ (SymmetricAlgebra.ι R M x) =
      Polynomial.C (SymmetricAlgebra.ι R M x) + φ x • (Polynomial.X : Polynomial A) :=
  SymmetricAlgebra.lift_ι_apply _ x

lemma left_inverse : (atZero R M).comp (translate R M φ) = AlgHom.id R A := by
  apply SymmetricAlgebra.algHom_ext
  ext x
  change atZero R M (translate R M φ (SymmetricAlgebra.ι R M x)) = SymmetricAlgebra.ι R M x
  rw [translate_generator,map_add,map_smul]
  change Polynomial.aevalTower (AlgHom.id R A) 0 (Polynomial.C (SymmetricAlgebra.ι R M x)) +
    φ x • Polynomial.aevalTower (AlgHom.id R A) 0 Polynomial.X = _
  rw [Polynomial.aevalTower_C,Polynomial.aevalTower_X,smul_zero,add_zero]
  rfl

lemma translate_injective : Function.Injective (translate R M φ) := by
  intro a b h
  have he := congrArg (atZero R M) h
  have ha := DFunLike.congr_fun (left_inverse R M φ) a
  have hb := DFunLike.congr_fun (left_inverse R M φ) b
  exact ha.symm.trans (he.trans hb)

/-- Multiplication by the actual symmetric generator of a split primitive
vector is injective. There is NO domain, reducedness or characteristic
hypothesis, and no assumed polynomial decomposition of the module. -/
theorem generator_regular (v : M) (hv : φ v=1) (a : A)
    (ha : a * SymmetricAlgebra.ι R M v=0) : a=0 := by
  have ht := congrArg (translate R M φ) ha
  rw [map_mul,map_zero,translate_generator,hv,one_smul] at ht
  have hm : (Polynomial.X + Polynomial.C (SymmetricAlgebra.ι R M v)) * translate R M φ a=0 := by
    simpa only [mul_comm,add_comm] using ht
  have hd := congrArg (fun p : Polynomial A => p /ₘ
    (Polynomial.X + Polynomial.C (SymmetricAlgebra.ι R M v))) hm
  rw [Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_add_C _),
    Polynomial.zero_divByMonic] at hd
  apply translate_injective R M φ
  simpa only [map_zero] using hd
end SymmetricPrimitiveRegular318
