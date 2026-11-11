module
public import ContactProjectivePointCover318
public section
noncomputable section
namespace ContactProjectivePointPresentation318
open AlgebraicGeometry CategoryTheory
open ContactQuotientChart318
variable (c : Fin 4 → ℚˣ) (n : ℕ) (S : CommRingCat.{0}) [Algebra ℚ S]
  (x : ContactProjectiveParameterPoint318.Point c n S)
variable (i : ContactProjectivePointCover318.index c n S x)
local notation "T" => ContactProjectivePointCover318.ring c n S x i
local notation "a" => ContactProjectivePointCover318.chart c n S x i
local notation "φ" => ContactProjectivePointCover318.coefficient c n S x i
@[expose] def ideal : Ideal c a T n :=
  (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) T).symm
    (ContactProjectivePointCover318.localPoint c n S x i)
lemma local_point : (ContactProjectiveParameterPoint318.ofIdeal c n T a (ideal c n S x i)).val=
    Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ x.val := by
  change (VaryingProjectiveQuotientEquiv318.equivalence ℚ (ring c a) (Fin n) T (ideal c n S x i)).val ≫
    ContactProjectiveQuotientParameter318.into c n a=_
  rw [ideal,Equiv.apply_symm_apply]
  exact ContactProjectivePointCover318.chart_square c n S x i
/-- EVERY global parameter point has a genuine presentation of its
actual universal fiber by full finite-projective original quotients. -/
@[expose] def data : ContactProjectiveLocalPresentation318.Data c n S
    (ContactProjectivePointFamily318.into c n S x) where
  coefficients := ContactProjectivePointCover318.coefficients c n S x
  chart := ContactProjectivePointCover318.chart c n S x
  ideal := ideal c n S x
  toFamily i := ContactProjectivePointLocalModel318.map c n S _ x
    (ContactProjectivePointCover318.coefficient c n S x i)
    (ContactProjectivePointCover318.chart c n S x i) (ideal c n S x i) (local_point c n S x i)
  cartesian i := ContactProjectivePointLocalModel318.cartesian c n S _ x
    (ContactProjectivePointCover318.coefficient c n S x i)
    (ContactProjectivePointCover318.chart c n S x i) (ideal c n S x i) (local_point c n S x i)
end ContactProjectivePointPresentation318
