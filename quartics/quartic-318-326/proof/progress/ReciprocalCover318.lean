module
public import ReciprocalJ318
public import LocalizedNormalModel318
public import Mathlib.RingTheory.RingHom.Etale
public section
noncomputable section
namespace ReciprocalCover318
open ReciprocalJ318
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false

lemma denominator_ne_zero (N:ℕ) (hN:N≠0) : ReciprocalJ318.denominator N≠0 := by
  unfold ReciprocalJ318.denominator
  apply mul_ne_zero
  · exact mul_ne_zero (mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr hN)) Polynomial.X_ne_zero
  · intro h
    have e:=congrArg (Polynomial.eval (0:ℤ)) h
    norm_num at e

variable (N:ℕ) (B:Type) [CommRing B] [Algebra (OpenJModel318.Base N) B]

/-- Actual reciprocal-chart cover homomorphism, using the constructed
isomorphism of the two localized polynomial base rings. -/
@[expose] def coverHom : ReciprocalJ318.Base N→+*B :=
  (algebraMap (OpenJModel318.Base N) B).comp (backward N)

/-- Its literal coordinate is the image of the inverse actual j-unit. -/
lemma coordinate : coverHom N B (ReciprocalJ318.coord N)=
    algebraMap (OpenJModel318.Base N) B (↑(zeroUnit N)⁻¹) := by
  simp [coverHom]

/-- Finiteness of the actual reciprocal cover is derived from the original
finite cover and a proved ring isomorphism. -/
theorem finite [Module.Finite (OpenJModel318.Base N) B] : (coverHom N B).Finite := by
  exact (RingHom.finite_algebraMap.mpr inferInstance).comp
    (reciprocalEquiv N).symm.finite

/-- The actual reciprocal cover is etale when the original cover is. -/
theorem etale [Algebra.Etale (OpenJModel318.Base N) B] : (coverHom N B).Etale := by
  exact RingHom.Etale.stableUnderComposition _ _
    (RingHom.Etale.of_bijective (reciprocalEquiv N).symm.bijective)
    (RingHom.etale_algebraMap.mpr inferInstance)

/-- The actual polynomial map on the reciprocal chart. -/
@[expose] def polynomialMap : Polynomial ℤ→+*B :=
  (coverHom N B).comp (algebraMap (Polynomial ℤ) (ReciprocalJ318.Base N))

lemma polynomial_coordinate : polynomialMap N B Polynomial.X =
    algebraMap (OpenJModel318.Base N) B (↑(zeroUnit N)⁻¹) :=
  coordinate N B

/-- The second actual affine normalization is finite and normal. The exact
polynomial scalar map is the reciprocal coordinate, rather than the original
j-coordinate reused accidentally. -/
theorem finite_normal_model [IsDomain B]
    [Module.Finite (OpenJModel318.Base N) B]
    [Algebra.Etale (OpenJModel318.Base N) B] (hN:N≠0) :
    letI := (polynomialMap N B).toAlgebra
    Module.Finite (Polynomial ℤ) (integralClosure (Polynomial ℤ) B) ∧
    IsIntegrallyClosed (integralClosure (Polynomial ℤ) B) ∧
    IsNoetherianRing (integralClosure (Polynomial ℤ) B) := by
  letI := (polynomialMap N B).toAlgebra
  letI := (coverHom N B).toAlgebra
  letI : IsScalarTower (Polynomial ℤ) (ReciprocalJ318.Base N) B :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  letI : Module.Finite (ReciprocalJ318.Base N) B := finite N B
  letI : Algebra.Etale (ReciprocalJ318.Base N) B := etale N B
  have h:=LocalizedNormalModel318.finite_normal_model (Rf:=ReciprocalJ318.Base N)
    (B:=B) (ReciprocalJ318.denominator N) (denominator_ne_zero N hN)
  exact ⟨h.1,h.2,LocalizedNormalModel318.model_noetherian (Rf:=ReciprocalJ318.Base N)
    (B:=B) (ReciprocalJ318.denominator N) (denominator_ne_zero N hN)⟩

end ReciprocalCover318
