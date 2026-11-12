module
public import OriginalNormalInfinityChart318
public section
noncomputable section
namespace OriginalNormalInfinityIntegralPoint318
open NumberField Polynomial ActualFinitePlaceIntegers318 AlgebraicGeometry CategoryTheory
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalInfinityOrder318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
local notation "R" => V c t w
local notation "P" => Polynomial R
local notation "B" => SourceOpenRing c t w D
local notation "C" => Order c t w D

/-- The original point map, not a chosen root or birational point,
evaluates the infinity polynomial coordinate at the literal inverse t. -/
lemma field_polynomial : M.fieldPoint.comp (polynomialMap c t w D)=
    (Polynomial.aeval (t:K c t)⁻¹).toRingHom := by
  apply Polynomial.ringHom_ext
  · intro r
    rw [RingHom.comp_apply,polynomial_C]
    simpa only [Polynomial.aeval_C] using
      OriginalNormalSourceCotangent318.field_scalar c t w D M r
  · rw [RingHom.comp_apply,polynomial_X,map_units_inv,
      OriginalNormalDualDifferential318.original_coordinate_unit]
    exact (Polynomial.aeval_X _).symm

variable (ht : w (t:K c t)⁻¹ ≤ 1)
@[expose] def integralCoordinate : R := ⟨(t:K c t)⁻¹,(bounded_iff w _).mp ht⟩

lemma polynomial_square :
    (algebraMap R (K c t)).comp (Polynomial.evalRingHom (integralCoordinate c t w ht))=
      M.fieldPoint.comp (polynomialMap c t w D) := by
  rw [field_polynomial]
  apply Polynomial.ringHom_ext
  · intro r
    rfl
  · rfl

include ht in
/-- Map each element's monic equation through the exact reciprocal
polynomial evaluation square. The reciprocal normal order is not assumed
to have an integral evaluation map. -/
lemma normal_value_integral (z : C) : IsIntegral R (M.fieldPoint (inclusion c t w D z)) := by
  letI := (polynomialMap c t w D).toAlgebra
  exact IsIntegral.map_of_comp_eq (Polynomial.evalRingHom (integralCoordinate c t w ht))
    M.fieldPoint (polynomial_square c t w D M ht)
    (IntegralClosureAlongRingMap318.integral (polynomialMap c t w D) z)

include ht in
lemma normal_value_bound (z : C) : w (M.fieldPoint (inclusion c t w D z)) ≤ 1 := by
  obtain ⟨r,hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral
    (normal_value_integral c t w D M ht z)
  rw [←hr]
  exact integer_bound w r

@[expose] def evaluation : C →+* R where
  toFun z := ⟨M.fieldPoint (inclusion c t w D z),
    (bounded_iff w _).mp (normal_value_bound c t w D M ht z)⟩
  map_zero' := Subtype.ext ((M.fieldPoint.comp (inclusion c t w D)).map_zero)
  map_one' := Subtype.ext ((M.fieldPoint.comp (inclusion c t w D)).map_one)
  map_add' x y := Subtype.ext ((M.fieldPoint.comp (inclusion c t w D)).map_add x y)
  map_mul' x y := Subtype.ext ((M.fieldPoint.comp (inclusion c t w D)).map_mul x y)

lemma field_square : (algebraMap R (K c t)).comp (evaluation c t w D M ht)=
    M.fieldPoint.comp (inclusion c t w D) := rfl

lemma polynomial (p : P) : evaluation c t w D M ht (polynomialScalar c t w D p)=
    Polynomial.evalRingHom (integralCoordinate c t w ht) p := by
  apply (IsFractionRing.injective R (K c t))
  change M.fieldPoint ((inclusion c t w D) (polynomialScalar c t w D p))=_
  change M.fieldPoint (polynomialMap c t w D p)=_
  exact (RingHom.congr_fun (polynomial_square c t w D M ht) p).symm

lemma retraction : (evaluation c t w D M ht).comp (scalar c t w D)=RingHom.id R := by
  ext r
  change evaluation c t w D M ht (polynomialScalar c t w D (Polynomial.C r))=r
  rw [polynomial]
  simp

lemma generic :
    Spec.map (CommRingCat.ofHom (algebraMap R (K c t))) ≫
      Spec.map (CommRingCat.ofHom (evaluation c t w D M ht)) ≫
        OriginalNormalInfinityChart318.chart c t w D M=
    Spec.map (CommRingCat.ofHom M.fieldPoint) ≫ M.source := by
  rw [←Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom
    ((algebraMap R (K c t)).comp (evaluation c t w D M ht))) ≫ _=_
  rw [field_square,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc,
    OriginalNormalInfinityChart318.source]
end OriginalNormalInfinityIntegralPoint318
