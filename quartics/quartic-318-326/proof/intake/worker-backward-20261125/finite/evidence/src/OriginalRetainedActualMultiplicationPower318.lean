module

public import OriginalActualOriginLieAddition318
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

@[expose] public section
noncomputable section

namespace OriginalRetainedActualMultiplicationPower318

open AlgebraicGeometry CategoryTheory MonoidalCategory
open OriginalAffineOriginCotangent318 OriginalAffineOriginFirstOrder318
open OriginalActualOriginAffineJet318 OriginalActualOriginLieAddition318
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
variable {A : Over (Spec (CommRingCat.of R))} [MonObj A] {e : B→ₐ[R] R}
variable (C : Chart R A e)

/-- Multiplication by n on the actual installed Scheme group,
using its categorical endomorphism power under pointwise product. -/
def installed (n : ℕ) : A ⟶ A := (𝟙 A)^n

theorem on_actual_points {S : Over (Spec (CommRingCat.of R))} (z : S ⟶ A) (n : ℕ) :
    z≫installed (A:=A) n=z^n := by
  rw [installed,MonObj.comp_pow,Category.comp_id]

theorem on_actual_origin (n : ℕ) : η[A]≫installed (A:=A) n=η[A] := by
  rw [on_actual_points,←MonObj.one_eq_one A,one_pow]

theorem actual_proper [IsProper A.hom] (n : ℕ) : IsProper (installed (A:=A) n).left := by
  letI : IsProper ((installed (A:=A) n).left≫A.hom) := by
    rw [(installed (A:=A) n).w]
    infer_instance
  exact IsProper.of_comp _ _

private theorem original_chart_zero {M : Type u} [AddCommGroup M] [Module R M] :
    (actual C (0 : Cot e→ₗ[R] M)).val=1 := by
  apply Over.OverMorphism.ext
  rw [actual_left,Hom.one_def,Over.comp_left,Over.toUnit_left,Over.mk_hom]
  have h : (points (S:=R) e (0 : Cot e→ₗ[R] M)).val=
      (Algebra.ofId R (Thick R M)).comp e := by
    apply AlgHom.ext
    intro b
    apply TrivSqZeroExt.ext
    · exact congrArg (fun f : B→ₐ[R] R => f b) ((points (S:=R) e (0 : Cot e→ₗ[R] M)).property)
    · rw [points_snd]
      rfl
  rw [h]
  change sp ((algebraMap R (Thick R M)).comp e.toRingHom)≫C.incl=
    sp (algebraMap R (Thick R M))≫(η[A]).left
  rw [←sp_comp,Category.assoc,C.origin]

private theorem original_chart_sum {M : Type u} [AddCommGroup M] [Module R M]
    (x y : Cot e→ₗ[R] M) :
    (actual C (x+y)).val=(actual C x).val*(actual C y).val := by
  rw [←operated_add C x y,operated,Equiv.apply_symm_apply]
  rfl

/-- Use the literal same thickened Scheme morphism as R74. No
generic tangent Lie group dictionary is assumed. -/
theorem actual_power_on_square_zero {M : Type u} [AddCommGroup M] [Module R M]
    (v : Cot e →ₗ[R] M) (n : ℕ) :
    (actual C v).val≫installed (A:=A) n=(actual C (n • v)).val := by
  rw [on_actual_points]
  induction n with
  | zero => rw [pow_zero,zero_nsmul,original_chart_zero]
  | succ n ih => rw [pow_succ,succ_nsmul,ih,original_chart_sum]

/-- The universal square-zero test with coefficients in the actual
cotangent module itself detects the full first jet, not just its
norm or determinant. This avoids any dual-separation assumption. -/
theorem original_universal_cotangent_point (n : ℕ) :
    (actual C (LinearMap.id : Cot e→ₗ[R] Cot e)).val≫installed (A:=A) n=
      (actual C (n • (LinearMap.id : Cot e→ₗ[R] Cot e))).val :=
  actual_power_on_square_zero C _ n

end OriginalRetainedActualMultiplicationPower318
