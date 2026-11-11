module
public import LocalizedRationalDifferentials318
public section
noncomputable section
namespace ThreeJCuspDifferentialCharts318
open AlgebraicGeometry CategoryTheory Polynomial
open ThreeProjectiveJCertificates318 LocalizedRationalDifferentials318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

@[expose] def finiteD : ℚ[X] := X^2-486*X-19683
@[expose] def reciprocalD : ℚ[X] := 1-486*X-19683*X^2
abbrev FiniteRing := Ring finiteNumerator
abbrev InfinityRing := Ring reciprocalNumerator
@[expose] def finiteInverse : FiniteRing := IsLocalization.Away.invSelf finiteNumerator
@[expose] def infinityInverse : InfinityRing := IsLocalization.Away.invSelf reciprocalNumerator
lemma finite_inverse : value finiteNumerator finiteNumerator*finiteInverse=1 :=
  IsLocalization.Away.mul_invSelf finiteNumerator
lemma infinity_inverse : value reciprocalNumerator reciprocalNumerator*infinityInverse=1 :=
  IsLocalization.Away.mul_invSelf reciprocalNumerator

lemma finite_wronskian : finiteDenominator.derivative*finiteNumerator-
    finiteDenominator*finiteNumerator.derivative= -X^2*(X+243)^2*finiteD := by
  simp only [finiteDenominator,finiteNumerator,finiteD,derivative_pow,derivative_mul,
    derivative_add,derivative_X,derivative_C,derivative_natCast,derivative_ofNat,pow_one,pow_zero,
    mul_one,one_mul,mul_zero,zero_mul,add_zero,zero_add]
  ring
lemma reciprocal_wronskian : reciprocalDenominator.derivative*reciprocalNumerator-
    reciprocalDenominator*reciprocalNumerator.derivative=(1+243*X)^2*reciprocalD := by
  simp only [reciprocalDenominator,reciprocalNumerator,reciprocalD,derivative_pow,
    derivative_mul,derivative_add,derivative_X,derivative_C,derivative_natCast,derivative_ofNat,
    derivative_one,pow_one,pow_zero,mul_one,one_mul,mul_zero,zero_mul,add_zero,zero_add]
  ring

@[expose] def finiteCofactor : FiniteRing :=
  -(value finiteNumerator X+243)^2*value finiteNumerator finiteD*finiteInverse^2
@[expose] def finiteJacobian : FiniteRing := (value finiteNumerator X)^2*finiteCofactor
@[expose] def infinityJacobian : InfinityRing :=
  (1+243*value reciprocalNumerator X)^2*value reciprocalNumerator reciprocalD*infinityInverse^2

lemma finite_coefficient :
    value finiteNumerator (finiteDenominator.derivative*finiteNumerator-
      finiteDenominator*finiteNumerator.derivative)*finiteInverse^2=finiteJacobian := by
  rw [finite_wronskian]
  simp only [map_neg,map_mul,map_pow,map_add,map_ofNat,finiteJacobian,finiteCofactor]
  ring
lemma infinity_coefficient :
    value reciprocalNumerator (reciprocalDenominator.derivative*reciprocalNumerator-
      reciprocalDenominator*reciprocalNumerator.derivative)*infinityInverse^2=infinityJacobian := by
  rw [reciprocal_wronskian]
  simp only [map_mul,map_pow,map_add,map_one,map_ofNat,infinityJacobian]

/-- Both missing source cusp charts carry an actual presentation for the
relative differential module of the reciprocal target coordinate 1/j. -/
@[expose] def finitePresentation :
    letI := targetAlgebra finiteDenominator finiteNumerator finiteInverse
    (FiniteRing ⧸ Ideal.span {finiteJacobian}) ≃ₗ[FiniteRing]
      KaehlerDifferential ℚ[X] FiniteRing := by
  letI := targetAlgebra finiteDenominator finiteNumerator finiteInverse
  rw [←finite_coefficient]
  exact relativePresentation finiteNumerator finiteDenominator finiteNumerator finiteInverse finite_inverse

@[expose] def infinityPresentation :
    letI := targetAlgebra reciprocalDenominator reciprocalNumerator infinityInverse
    (InfinityRing ⧸ Ideal.span {infinityJacobian}) ≃ₗ[InfinityRing]
      KaehlerDifferential ℚ[X] InfinityRing := by
  letI := targetAlgebra reciprocalDenominator reciprocalNumerator infinityInverse
  rw [←infinity_coefficient]
  exact relativePresentation reciprocalNumerator reciprocalDenominator reciprocalNumerator
    infinityInverse infinity_inverse

@[expose] def finiteEmbedding : Spec (CommRingCat.of FiniteRing) ⟶ ProjectiveJLine318.scheme ℚ :=
  RationalPairLocalMaps318.numeratorBase finiteNumerator ≫ JLineAtlas318.chart ℚ 1
@[expose] def infinityEmbedding : Spec (CommRingCat.of InfinityRing) ⟶ ProjectiveJLine318.scheme ℚ :=
  RationalPairLocalMaps318.numeratorBase reciprocalNumerator ≫ JLineAtlas318.chart ℚ 0
instance finiteEmbedding_open : IsOpenImmersion finiteEmbedding := by unfold finiteEmbedding; infer_instance
instance infinityEmbedding_open : IsOpenImmersion infinityEmbedding := by unfold infinityEmbedding; infer_instance

theorem finite_scheme_square : finiteEmbedding ≫ ThreeProjectiveJMap318.map=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ)
      (targetCoordinate finiteDenominator finiteNumerator finiteInverse)).toRingHom) ≫
        JLineAtlas318.chart ℚ 0 := by
  rw [finiteEmbedding,Category.assoc,ThreeProjectiveJMap318.finite_restriction]
  change RationalPairLocalMaps318.numeratorBase finiteNumerator ≫
    RationalPairGluing318.map finiteNumerator finiteDenominator finite_coprime=_
  rw [RationalPairGluing318.numerator_restriction]
  rfl
theorem infinity_scheme_square : infinityEmbedding ≫ ThreeProjectiveJMap318.map=
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ)
      (targetCoordinate reciprocalDenominator reciprocalNumerator infinityInverse)).toRingHom) ≫
        JLineAtlas318.chart ℚ 0 := by
  rw [infinityEmbedding,Category.assoc,ThreeProjectiveJMap318.reciprocal_restriction]
  change RationalPairLocalMaps318.numeratorBase reciprocalNumerator ≫
    RationalPairGluing318.map reciprocalNumerator reciprocalDenominator reciprocal_coprime=_
  rw [RationalPairGluing318.numerator_restriction]
  rfl

@[expose] def finiteEvaluation : FiniteRing →ₐ[ℚ] ℚ :=
  IsLocalization.Away.liftAlgHom (f:=Polynomial.aeval (R:=ℚ) (0:ℚ)) finiteNumerator
    (by norm_num [finiteNumerator,isUnit_iff_ne_zero])
@[expose] def infinityEvaluation : InfinityRing →ₐ[ℚ] ℚ :=
  IsLocalization.Away.liftAlgHom (f:=Polynomial.aeval (R:=ℚ) (0:ℚ)) reciprocalNumerator
    (by norm_num [reciprocalNumerator])
lemma finiteEvaluation_value (p : ℚ[X]) : finiteEvaluation (value finiteNumerator p)=p.eval 0 := by
  simp only [finiteEvaluation,value,IsScalarTower.toAlgHom_apply,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,Polynomial.aeval_def]
  simp
lemma infinityEvaluation_value (p : ℚ[X]) : infinityEvaluation (value reciprocalNumerator p)=p.eval 0 := by
  simp only [infinityEvaluation,value,IsScalarTower.toAlgHom_apply,
    IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq,Polynomial.aeval_def]
  simp

lemma finiteEvaluation_inverse : finiteEvaluation finiteInverse=1/(3:ℚ)^18 := by
  have h := congrArg finiteEvaluation finite_inverse
  simp only [map_mul,map_one,finiteEvaluation_value] at h
  norm_num [finiteNumerator] at h ⊢
  linarith
lemma infinityEvaluation_inverse : infinityEvaluation infinityInverse=1 := by
  have h := congrArg infinityEvaluation infinity_inverse
  simpa [infinityEvaluation_value,reciprocalNumerator] using h

/-- The finite cusp has a double Jacobian zero with a proved nonzero
cofactor; the reciprocal origin has a unit Jacobian value. -/
theorem cusp_jacobian_values :
    finiteEvaluation finiteCofactor=1/(3:ℚ)^17 ∧
    infinityEvaluation infinityJacobian=1 := by
  constructor
  · norm_num [finiteCofactor,map_mul,map_neg,map_add,map_pow,
      finiteEvaluation_value,finiteEvaluation_inverse,finiteD]
  · norm_num [infinityJacobian,map_mul,map_add,map_pow,
      infinityEvaluation_value,infinityEvaluation_inverse,reciprocalD]

end ThreeJCuspDifferentialCharts318
