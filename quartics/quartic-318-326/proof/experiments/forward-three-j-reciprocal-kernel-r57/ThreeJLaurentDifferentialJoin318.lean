module
public import ThreeJRamificationIdealCharts318
public section
noncomputable section
namespace ThreeJLaurentDifferentialJoin318
open Polynomial ThreeJLaurentEquiv318 ThreeJRelativeDifferentials318
open ThreeProjectiveJCertificates318 LocalizedRationalDifferentials318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma denominator_inverse : value (X:ℚ[X]) finiteDenominator*
    ProjectiveLineOverlap318.s^3=1 := by
  change algebraMap ℚ[X] Laurent (X^3)*ProjectiveLineOverlap318.s^3=1
  rw [map_pow]
  change ProjectiveLineOverlap318.t^3*ProjectiveLineOverlap318.s^3=1
  rw [←mul_pow,ProjectiveLineOverlap318.ts,one_pow]

lemma actual_coordinate : targetCoordinate finiteNumerator (X:ℚ[X])
    (ProjectiveLineOverlap318.s^3)=jLaurent := by
  simp only [targetCoordinate,finiteNumerator,map_mul,map_add,map_pow,map_ofNat]
  rfl

lemma actual_algebra : targetAlgebra finiteNumerator (X:ℚ[X])
    (ProjectiveLineOverlap318.s^3)=ThreeJFiniteLaurentMap318.jAlgebra := by
  unfold targetAlgebra
  rw [actual_coordinate]
  rfl

/-- Comparison of the actual framed differential coefficient with the
transported monic annihilator ideal. The extra Laurent unit is retained
until the ideal equality is proved. -/
lemma literal_coefficient_ideal :
    Ideal.span (Set.singleton (value (X:ℚ[X])
      (finiteNumerator.derivative*finiteDenominator-
        finiteNumerator*finiteDenominator.derivative)*(ProjectiveLineOverlap318.s^3)^2))=
      originalDifferentialIdeal := by
  have hpoly : finiteNumerator.derivative*finiteDenominator-
      finiteNumerator*finiteDenominator.derivative=
      X^2*(X+243)^2*ThreeJCuspDifferentialCharts318.finiteD := by
    linear_combination -ThreeJCuspDifferentialCharts318.finite_wronskian
  have he : value (X:ℚ[X])
      (finiteNumerator.derivative*finiteDenominator-
        finiteNumerator*finiteDenominator.derivative)*(ProjectiveLineOverlap318.s^3)^2=
      ThreeJDerivativeOpen318.derivativeImage*ProjectiveLineOverlap318.s^3 := by
    rw [hpoly,ThreeJDerivativeOpen318.derivative_factorization]
    simp only [map_mul,map_pow,map_add,map_sub,map_ofNat,ThreeJCuspDifferentialCharts318.finiteD]
    change ProjectiveLineOverlap318.t^2*(ProjectiveLineOverlap318.t+243)^2*
        (ProjectiveLineOverlap318.t^2-486*ProjectiveLineOverlap318.t-19683)*
          (ProjectiveLineOverlap318.s^3)^2=
      ProjectiveLineOverlap318.s*(ProjectiveLineOverlap318.t+243)^2*
        (ProjectiveLineOverlap318.t^2-486*ProjectiveLineOverlap318.t-19683)*
          ProjectiveLineOverlap318.s^3
    have hts : ProjectiveLineOverlap318.t^2*ProjectiveLineOverlap318.s^2=1 := by
      rw [←mul_pow,ProjectiveLineOverlap318.ts,one_pow]
    linear_combination (ProjectiveLineOverlap318.t+243)^2*
      (ProjectiveLineOverlap318.t^2-486*ProjectiveLineOverlap318.t-19683)*
      ProjectiveLineOverlap318.s^4*hts
  have hs : IsUnit ProjectiveLineOverlap318.s :=
    IsUnit.of_mul_eq_one_right _ ProjectiveLineOverlap318.ts
  rw [he]
  change Ideal.span {(ThreeJDerivativeOpen318.derivativeImage * ProjectiveLineOverlap318.s^3)} =
    originalDifferentialIdeal
  rw [Ideal.span_singleton_mul_right_unit (hs.pow 3),original_ideal_generator]

/-- The earlier monic differential ideal is now a presentation of the
literal original Laurent Kaehler module under the actual j pullback. -/
@[expose] def literalLaurentPresentation :
    letI := ThreeJFiniteLaurentMap318.jAlgebra
    (Laurent ⧸ originalDifferentialIdeal) ≃ₗ[Laurent]
      KaehlerDifferential ThreeJMonicAlgebra318.Base Laurent := by
  letI := ThreeJFiniteLaurentMap318.jAlgebra
  have e :
      letI := targetAlgebra finiteNumerator (X:ℚ[X]) (ProjectiveLineOverlap318.s^3)
      (Laurent ⧸ Ideal.span (Set.singleton (value (X:ℚ[X])
        (finiteNumerator.derivative*finiteDenominator-
          finiteNumerator*finiteDenominator.derivative)*(ProjectiveLineOverlap318.s^3)^2))) ≃ₗ[Laurent]
        KaehlerDifferential ℚ[X] Laurent :=
    relativePresentation finiteDenominator finiteNumerator (X:ℚ[X])
      (ProjectiveLineOverlap318.s^3) denominator_inverse
  rw [actual_algebra,literal_coefficient_ideal] at e
  exact e

end ThreeJLaurentDifferentialJoin318
