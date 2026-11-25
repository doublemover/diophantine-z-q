module
public import OriginalAffineReesChartLocal318
public section
noncomputable section

namespace OriginalR47ReesCoefficientMap318

open Polynomial HomogeneousLocalization Graded
open OriginalAffineReesGrading318 OriginalAffineReesBlowup318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A B : Type*} [CommRing A] [CommRing B]
variable (I : Ideal A) (f : A →+* B)

/-- Coefficient extension on the literal pinned Rees algebras.
The ideal is exactly the image ideal; there is no freely chosen grading
or cast from a polynomial incidence ring. -/
@[expose] def mapRing : Rees I →+* Rees (I.map f) :=
  ((Polynomial.mapRingHom f).comp (Subalgebra.val (reesAlgebra I)).toRingHom).codRestrict
    (reesAlgebra (I.map f)) (fun z n => by
      change ((z.val).map f).coeff n ∈ (I.map f)^n
      rw [Polynomial.coeff_map, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem f (z.property n))

@[expose] def mapGraded : grade I →+*ᵍ grade (I.map f) where
  toRingHom := mapRing I f
  map_mem := by
    intro n z hz j hj
    change ((z.val).map f).coeff j = 0
    rw [Polynomial.coeff_map, hz j hj, map_zero]

/-- Each chosen degree-one generator remains that literal generator in
the new Rees, including x, y and the arithmetic uniformizer in R40. -/
theorem generator_read (a : A) (ha : a ∈ I) :
    mapGraded I f (generator I a ha) =
      generator (I.map f) (f a) (Ideal.mem_map_of_mem f ha) := by
  apply Subtype.ext
  change (monomial 1 a).map f = monomial 1 (f a)
  exact Polynomial.map_monomial (n := 1) (a := a) f

/-- The coefficient extension as an actual map between the two
homogeneous localizations. The denominator is not reselected. -/
@[expose] def chartMap (a : A) (ha : a ∈ I) :
    chart I a ha →+* chart (I.map f) (f a) (Ideal.mem_map_of_mem f ha) :=
  HomogeneousLocalization.map (mapGraded I f) (by
    intro x hx
    obtain ⟨n,rfl⟩ := hx
    change mapGraded I f ((generator I a ha)^n) ∈
      Submonoid.powers (generator (I.map f) (f a) (Ideal.mem_map_of_mem f ha))
    rw [map_pow, generator_read]
    exact ⟨n,rfl⟩)

/-- All homogeneous numerator coordinates are preserved before
localization; the target numerator is in the power of the *mapped* ideal. -/
theorem homogeneous_read (n : ℕ) (a : A) (ha : a ∈ I^n) :
    mapGraded I f (homogeneous I n a ha).val =
      (homogeneous (I.map f) n (f a)
        (by
          rw [← Ideal.map_pow]
          exact Ideal.mem_map_of_mem f ha)).val := by
  apply Subtype.ext
  change (monomial n a).map f = monomial n (f a)
  exact Polynomial.map_monomial (n := n) (a := a) f

end OriginalR47ReesCoefficientMap318

#print axioms OriginalR47ReesCoefficientMap318.mapGraded
#print axioms OriginalR47ReesCoefficientMap318.generator_read
#print axioms OriginalR47ReesCoefficientMap318.chartMap
#print axioms OriginalR47ReesCoefficientMap318.homogeneous_read
