module
public import ContactReciprocalBase318
public import LocalizedNormalModel318
public import Mathlib.RingTheory.RingHom.Etale
public section
noncomputable section
namespace ContactReciprocalCover318
open ContactReciprocalBase318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

variable (B:Type) [CommRing B] [Algebra ContactKummerOrder318.OpenBase B]

/-- Actual reciprocal-chart cover homomorphism, using the constructed
isomorphism of the two localized polynomial base rings. -/
@[expose] def coverHom : ContactReciprocalBase318.Base→+*B :=
  (algebraMap ContactKummerOrder318.OpenBase B).comp backward

/-- Its literal coordinate is the image of the inverse actual t-unit. -/
lemma coordinate : coverHom B s=
    algebraMap ContactKummerOrder318.OpenBase B (↑tUnit⁻¹) := by
  simp [coverHom]

/-- Finiteness of the actual reciprocal cover is derived from the original
finite cover and a proved ring isomorphism. -/
theorem finite [Module.Finite ContactKummerOrder318.OpenBase B] : (coverHom B).Finite := by
  exact (RingHom.finite_algebraMap.mpr inferInstance).comp
    reciprocalEquiv.symm.finite

/-- The actual reciprocal cover is etale when the original cover is. -/
theorem etale [Algebra.Etale ContactKummerOrder318.OpenBase B] : (coverHom B).Etale := by
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective reciprocalEquiv.symm.bijective)
    (RingHom.etale_algebraMap.mpr inferInstance)

/-- The actual polynomial map on the reciprocal chart. -/
@[expose] def polynomialMap : Polynomial ℚ→+*B :=
  (coverHom B).comp (algebraMap (Polynomial ℚ) (ContactReciprocalBase318.Base))

lemma polynomial_coordinate : polynomialMap B Polynomial.X =
    algebraMap ContactKummerOrder318.OpenBase B (↑tUnit⁻¹) :=
  coordinate B

/-- The second actual affine normalization is finite and normal. The exact
polynomial scalar map is the reciprocal coordinate, rather than the original
t-coordinate reused accidentally. -/
theorem finite_normal_model [IsDomain B]
    [Module.Finite ContactKummerOrder318.OpenBase B]
    [Algebra.Etale ContactKummerOrder318.OpenBase B] :
    letI := (polynomialMap B).toAlgebra
    Module.Finite (Polynomial ℚ) (integralClosure (Polynomial ℚ) B) ∧
    IsIntegrallyClosed (integralClosure (Polynomial ℚ) B) ∧
    IsNoetherianRing (integralClosure (Polynomial ℚ) B) := by
  letI := (polynomialMap B).toAlgebra
  letI := (coverHom B).toAlgebra
  letI : IsScalarTower (Polynomial ℚ) (ContactReciprocalBase318.Base) B :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Module.Finite (ContactReciprocalBase318.Base) B := finite B
  letI : Algebra.Etale (ContactReciprocalBase318.Base) B := etale B
  have h:=LocalizedNormalModel318.finite_normal_model (Rf:=ContactReciprocalBase318.Base)
    (B:=B) ContactReciprocalBase318.denominator ContactReciprocalBase318.denominator_ne_zero
  exact ⟨h.1,h.2,LocalizedNormalModel318.model_noetherian (Rf:=ContactReciprocalBase318.Base)
    (B:=B) ContactReciprocalBase318.denominator ContactReciprocalBase318.denominator_ne_zero⟩


/-- The original t-chart comparison is kept generic in the source algebra
so its actual scalar structure is not confused with a tensor-factor action. -/
theorem original_finite_normal_model [IsDomain B]
    [Module.Finite ContactKummerOrder318.OpenBase B]
    [Algebra.Etale ContactKummerOrder318.OpenBase B] :
    letI := ((algebraMap ContactKummerOrder318.OpenBase B).comp
      (algebraMap (Polynomial ℚ) ContactKummerOrder318.OpenBase)).toAlgebra
    Module.Finite (Polynomial ℚ) (integralClosure (Polynomial ℚ) B) ∧
    IsIntegrallyClosed (integralClosure (Polynomial ℚ) B) ∧
    IsNoetherianRing (integralClosure (Polynomial ℚ) B) := by
  letI := ((algebraMap ContactKummerOrder318.OpenBase B).comp
    (algebraMap (Polynomial ℚ) ContactKummerOrder318.OpenBase)).toAlgebra
  letI : IsScalarTower (Polynomial ℚ) ContactKummerOrder318.OpenBase B :=
    IsScalarTower.of_algebraMap_eq (fun _=>rfl)
  have h:=LocalizedNormalModel318.finite_normal_model (Rf:=ContactKummerOrder318.OpenBase)
    (B:=B) ContactKummerOrder318.denominator ContactKummerOrder318.denominator_ne_zero
  exact ⟨h.1,h.2,LocalizedNormalModel318.model_noetherian (Rf:=ContactKummerOrder318.OpenBase)
    (B:=B) ContactKummerOrder318.denominator ContactKummerOrder318.denominator_ne_zero⟩

end ContactReciprocalCover318
