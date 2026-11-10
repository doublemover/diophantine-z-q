module
public import RationalPairGluing318
public section
noncomputable section
namespace ThreeAffineJMaps318
open AlgebraicGeometry CategoryTheory Polynomial ThreeProjectiveJCertificates318

/-- The actual j scheme morphism on the entire finite source affine line.
At T=0 it uses the reciprocal target chart rather than dividing by zero. -/
@[expose] def finiteMap : Spec (CommRingCat.of ℚ[X]) ⟶ ProjectiveJLine318.scheme ℚ :=
  RationalPairGluing318.map finiteNumerator finiteDenominator finite_coprime

/-- The actual j scheme morphism on the entire reciprocal source affine line,
including S=0, which is the original projective source infinity. -/
@[expose] def reciprocalMap : Spec (CommRingCat.of ℚ[X]) ⟶ ProjectiveJLine318.scheme ℚ :=
  RationalPairGluing318.map reciprocalNumerator reciprocalDenominator reciprocal_coprime

@[reassoc] theorem finite_numerator :
    RationalPairLocalMaps318.numeratorBase finiteNumerator ≫ finiteMap =
      RationalPairLocalMaps318.numeratorMap finiteNumerator finiteDenominator :=
  RationalPairGluing318.numerator_restriction _ _ _

@[reassoc] theorem finite_denominator :
    RationalPairLocalMaps318.denominatorBase finiteDenominator ≫ finiteMap =
      RationalPairLocalMaps318.denominatorMap finiteNumerator finiteDenominator :=
  RationalPairGluing318.denominator_restriction _ _ _

@[reassoc] theorem reciprocal_numerator :
    RationalPairLocalMaps318.numeratorBase reciprocalNumerator ≫ reciprocalMap =
      RationalPairLocalMaps318.numeratorMap reciprocalNumerator reciprocalDenominator :=
  RationalPairGluing318.numerator_restriction _ _ _

@[reassoc] theorem reciprocal_denominator :
    RationalPairLocalMaps318.denominatorBase reciprocalDenominator ≫ reciprocalMap =
      RationalPairLocalMaps318.denominatorMap reciprocalNumerator reciprocalDenominator :=
  RationalPairGluing318.denominator_restriction _ _ _

@[reassoc] theorem finite_over_Q : finiteMap ≫ ProjectiveJLine318.structureMap ℚ =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])) :=
  RationalPairGluing318.over_Q _ _ _

@[reassoc] theorem reciprocal_over_Q : reciprocalMap ≫ ProjectiveJLine318.structureMap ℚ =
    Spec.map (CommRingCat.ofHom (algebraMap ℚ ℚ[X])) :=
  RationalPairGluing318.over_Q _ _ _

end ThreeAffineJMaps318
