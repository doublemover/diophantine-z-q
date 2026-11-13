module
public import OriginalNormalOrderChart318
public import OriginalNormalizationIntegralEvaluation318
public section
noncomputable section
namespace OriginalNormalOrderIntegralPoint318
open AlgebraicGeometry CategoryTheory NumberField Polynomial ActualFinitePlaceIntegers318
open OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318 OriginalAllPlaceNormalModel318
open OriginalNormalOrderChart318 OriginalNormalizationIntegralEvaluation318
variable (c : Fin 4 → ℚˣ) (t : ℚ) (w : FinitePlace (K c t))
  (D : OriginalAllPlaceNormalizedData318.Data c t w) (M : Realization c t w D)
  (ht : w (t : K c t) ≤ 1)
local notation "R" => V c t w
local notation "C" => Order c t w D
local notation "B" => SourceOpenRing c t w D

/-- Literal original field evaluation restricted to the entire normal
order and factored through the actual valuation ring by proved integrality. -/
@[expose] def evaluation : C →+* R where
  toFun z := ⟨M.fieldPoint z.val,(bounded_iff w _).mp (normal_value_bound c t w D M ht z)⟩
  map_zero' := Subtype.ext (M.fieldPoint.map_zero)
  map_one' := Subtype.ext (M.fieldPoint.map_one)
  map_add' x y := Subtype.ext (M.fieldPoint.map_add x.val y.val)
  map_mul' x y := Subtype.ext (M.fieldPoint.map_mul x.val y.val)

lemma field_square : (algebraMap R (K c t)).comp (evaluation c t w D M ht)=
    M.fieldPoint.comp
      (IntegralFourRootNormalizationConductor318.normalOrder R
        (contacts c t w) D.coefficients).val.toRingHom := rfl

lemma polynomial (p : R[X]) :
    evaluation c t w D M ht (algebraMap R[X] C p)=
      Polynomial.evalRingHom (integralCoordinate c t w ht) p := by
  apply (IsFractionRing.injective R (K c t))
  change M.fieldPoint (algebraMap R[X] B p)=_
  exact (RingHom.congr_fun (polynomial_square c t w D M ht) p).symm

lemma retraction : (evaluation c t w D M ht).comp (scalar c t w D)=RingHom.id R := by
  ext r
  change evaluation c t w D M ht (algebraMap R[X] C (Polynomial.C r))=r
  rw [polynomial]
  simp

/-- The entire original signed field point factors through this actual
normal-order point and its proved open chart on M. -/
theorem generic :
    Spec.map (CommRingCat.ofHom (algebraMap R (K c t))) ≫
      Spec.map (CommRingCat.ofHom (evaluation c t w D M ht)) ≫ chart c t w D M=
    Spec.map (CommRingCat.ofHom M.fieldPoint) ≫ M.source := by
  rw [←Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom
    ((algebraMap R (K c t)).comp (evaluation c t w D M ht))) ≫ chart c t w D M=_
  rw [field_square,CommRingCat.ofHom_comp,Spec.map_comp,Category.assoc,
    OriginalNormalOrderChart318.source]
end OriginalNormalOrderIntegralPoint318
