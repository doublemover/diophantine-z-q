module
public import ContactRelativeFiniteCohomologyModel318
public import ContactRelativeTwistCoefficientScalar318
public import ContactCoefficientNativeSections318
public section
noncomputable section
namespace ContactCoefficientCoordinatePowers318
open AlgebraicGeometry CategoryTheory LineSheafClass318 TensorProduct
open ContactOriginalRelativePolynomialCharts318 ContactOriginalRelativeLineOverlap318
open ContactOriginalCoefficientActions318 ContactCoefficientNativeSections318
open ContactRelativeCoefficientChange318
open scoped TensorProduct
set_option maxHeartbeats 850000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (R S : CommRingCat.{0}) [Algebra ℚ R] [Algebra ℚ S]
  (f : R →ₐ[ℚ] S) (c : Fin 4 → ℚˣ) (L : Line (curve R c))
local instance : Algebra R S := f.toAlgebra
local instance : Module R (infinitySections R c L) := infinityModule R c L
local instance : Module S (infinitySections S c (L' R S f c L)) := infinityModule S c _
local instance : Module R (originalSections R c L) := overlapModule R c L
local instance : Module S (originalSections S c (L' R S f c L)) := overlapModule S c _
local instance : Module (LaurentPolynomial R) (originalSections R c L) := overlapLaurentModule R c L
local instance : Module (LaurentPolynomial S) (originalSections S c (L' R S f c L)) := overlapLaurentModule S c _
local instance : IsScalarTower ℚ (Polynomial ℚ) (infinityRing c) :=
  IsScalarTower.of_algebraMap_eq' (RingHom.ext_rat _ _)

lemma infinity_ring_power (n : ℕ) : infinityRingMap R S f c
    (RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R (infinityRing c) (Polynomial.X ^ n)) =
    RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ S (infinityRing c) (Polynomial.X ^ n) := by
  rw [map_pow,map_pow,map_pow]
  congr 1
  rw [RelativeOriginalPolynomialAlgebra318.polynomialMap_X,
    RelativeCoefficientChange318.ringMap_tmul,map_one,
    RelativeOriginalPolynomialAlgebra318.polynomialMap_X]

lemma infinity_restriction_power (n : ℕ) (x : infinitySections R c L) :
    ContactCoefficientLineCharts318.infinityRestriction R S f c L ((Polynomial.X ^ n : Polynomial R) • x) =
      (Polynomial.X ^ n : Polynomial S) • ContactCoefficientLineCharts318.infinityRestriction R S f c L x := by
  change ContactCoefficientLineCharts318.infinityRestriction R S f c L
    (RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ R (infinityRing c) (Polynomial.X ^ n) • x)=
    RelativeOriginalPolynomialAlgebra318.polynomialMap ℚ S (infinityRing c) (Polynomial.X ^ n) • _
  rw [OriginalCoefficientChartLine318.scalar,infinity_ring_power]

lemma overlap_restriction_shift (d : ℤ) (x : originalSections R c L) :
    ContactCoefficientLineCharts318.overlapRestriction R S f c L ((LaurentPolynomial.T d : LaurentPolynomial R) • x)=
      (LaurentPolynomial.T d : LaurentPolynomial S) • ContactCoefficientLineCharts318.overlapRestriction R S f c L x := by
  change ContactCoefficientLineCharts318.overlapRestriction R S f c L
    (ContactOriginalRelativeOverlapCoordinates318.laurentMap R c (LaurentPolynomial.T d) • x)=
    ContactOriginalRelativeOverlapCoordinates318.laurentMap S c (LaurentPolynomial.T d) • _
  rw [OriginalCoefficientChartLine318.scalar,ContactRelativeTwistCoefficientScalar318.ring_monomial]

/-- The original coefficient-only infinity section equivalence preserves
the actual coordinate-power action, not a newly chosen jet presentation. -/
lemma infinity_square (b : ℕ) :
    (infinityEquivalence R S f c L).toLinearMap.comp ((ContactRelativeInfinityJet318.power R c L b).baseChange S)=
    (ContactRelativeInfinityJet318.power S c (L' R S f c L) b).comp
      (infinityEquivalence R S f c L).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro s x
  change infinityEquivalence R S f c L (s ⊗ₜ[R] ((Polynomial.X ^ (b+1) : Polynomial R) • x))=
    (Polynomial.X ^ (b+1) : Polynomial S) • infinityEquivalence R S f c L (s ⊗ₜ[R] x)
  rw [infinity_pure,infinity_pure,infinity_restriction_power]
  change (Polynomial.C s : Polynomial S) • ((Polynomial.X ^ (b+1) : Polynomial S) • _) =
    (Polynomial.X ^ (b+1) : Polynomial S) • ((Polynomial.C s : Polynomial S) • _)
  exact smul_comm _ _ _

lemma overlap_square (d : ℤ) :
    (overlapEquivalence R S f c L).toLinearMap.comp
      ((ContactRelativeTwistKernel318.shift R c L d).toLinearMap.baseChange S)=
    (ContactRelativeTwistKernel318.shift S c (L' R S f c L) d).toLinearMap.comp
      (overlapEquivalence R S f c L).toLinearMap := by
  apply AlgebraTensorModule.ext
  intro s x
  change overlapEquivalence R S f c L (s ⊗ₜ[R] ((LaurentPolynomial.T d : LaurentPolynomial R) • x))=
    (LaurentPolynomial.T d : LaurentPolynomial S) • overlapEquivalence R S f c L (s ⊗ₜ[R] x)
  rw [overlap_pure,overlap_pure,overlap_restriction_shift]
  change (LaurentPolynomial.C s : LaurentPolynomial S) • ((LaurentPolynomial.T d : LaurentPolynomial S) • _) =
    (LaurentPolynomial.T d : LaurentPolynomial S) • ((LaurentPolynomial.C s : LaurentPolynomial S) • _)
  exact smul_comm _ _ _
end ContactCoefficientCoordinatePowers318
