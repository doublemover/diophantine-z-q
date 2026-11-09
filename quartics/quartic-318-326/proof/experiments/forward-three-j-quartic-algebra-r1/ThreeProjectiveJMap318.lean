module
public import ThreeAffineJMaps318
public import RationalPairDenominatorEvaluation318
public import ProjectiveLineOverlap318
public section
noncomputable section
namespace ThreeProjectiveJMap318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
open ThreeProjectiveJCertificates318 ThreeAffineJMaps318 ProjectiveLineOverlap318
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

lemma evaluation_t : (Polynomial.aeval (R:=ℚ) t).toRingHom = algebraMap ℚ[X] A := by
  apply Polynomial.ringHom_ext
  · intro q
    simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_C,
      Polynomial.algebraMap_eq] using IsScalarTower.algebraMap_apply ℚ ℚ[X] A q
  · simp only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,Polynomial.aeval_X,t]

lemma finite_denominator_inverse : Polynomial.aeval (R:=ℚ) t finiteDenominator * s^3=1 := by
  simpa only [finiteDenominator,map_pow,Polynomial.aeval_X,←mul_pow,ts,one_pow]

lemma reciprocal_denominator_inverse :
    Polynomial.aeval (R:=ℚ) s reciprocalDenominator * t=1 := by
  simpa only [reciprocalDenominator,Polynomial.aeval_X,mul_comm] using ts

/-- The two finite target coordinates are exactly equal on the actual
Laurent source overlap. The common degree-four scalar is canceled only using
the explicitly proved TS=1 identity in this ring. -/
lemma overlap_coordinate :
    Polynomial.aeval (R:=ℚ) t finiteNumerator * s^3 =
      Polynomial.aeval (R:=ℚ) s reciprocalNumerator * t := by
  simp only [finiteNumerator,reciprocalNumerator,map_mul,map_add,map_pow,map_one,
    map_ofNat,Polynomial.aeval_X]
  have hn : (t+27)*(t+243)^3 = t^4*((1+27*s)*(1+243*s)^3) := by
    simpa only [homogeneousNumerator,mul_one] using (chart_pair_overlap t s ts).1
  rw [hn]
  calc
    _ = ((1+27*s)*(1+243*s)^3)*t*(t*s)^3 := by ring
    _ = ((1+27*s)*(1+243*s)^3)*t := by rw [ts,one_pow,mul_one]

/-- Equality on the actual projective-source intersection, not just on a
dense subopen or on complex-valued points. Both denominators are units on
this entire Laurent overlap, so both maps use the finite target chart. -/
theorem affine_overlap : finiteInclusion ≫ finiteMap = infinityInclusion ≫ reciprocalMap := by
  change Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] A)) ≫ finiteMap =
    Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) s).toRingHom) ≫ reciprocalMap
  rw [←evaluation_t]
  unfold finiteMap reciprocalMap
  rw [RationalPairDenominatorEvaluation318.evaluation_formula _ _ _
    (Polynomial.aeval (R:=ℚ) t) (s^3) finite_denominator_inverse,
    RationalPairDenominatorEvaluation318.evaluation_formula _ _ _
    (Polynomial.aeval (R:=ℚ) s) t reciprocal_denominator_inverse,
    overlap_coordinate]

@[expose] def localMap : (i : Fin 2) → (JLineAtlas318.cover ℚ).X i ⟶
    ProjectiveJLine318.scheme ℚ := Fin.cases reciprocalMap (fun _ => finiteMap)

lemma compatible (i j : Fin 2) :
    pullback.fst ((JLineAtlas318.cover ℚ).f i) ((JLineAtlas318.cover ℚ).f j) ≫ localMap i =
      pullback.snd _ _ ≫ localMap j := by
  fin_cases i <;> fin_cases j
  · exact RationalPairGluing318.diagonal_compatibility _ _
  · exact RationalPairGluing318.compatibility_of_pullback actual_pullback _ _ affine_overlap.symm
  · exact RationalPairGluing318.compatibility_of_pullback actual_pullback.flip _ _ affine_overlap
  · exact RationalPairGluing318.diagonal_compatibility _ _

/-- The actual global level-three j morphism from the original projective
line over Q, constructed by gluing the exact rational coordinate maps. -/
@[expose] def map : ProjectiveJLine318.scheme ℚ ⟶ ProjectiveJLine318.scheme ℚ :=
  (JLineAtlas318.cover ℚ).glueMorphisms localMap compatible

@[reassoc] theorem reciprocal_restriction :
    JLineAtlas318.chart ℚ 0 ≫ map = reciprocalMap :=
  (JLineAtlas318.cover ℚ).ι_glueMorphisms localMap compatible 0

@[reassoc] theorem finite_restriction :
    JLineAtlas318.chart ℚ 1 ≫ map = finiteMap :=
  (JLineAtlas318.cover ℚ).ι_glueMorphisms localMap compatible 1

/-- The projective map has the original rational coefficient map. No
extension of this model across characteristic 3 is asserted. -/
@[reassoc] theorem over_Q : map ≫ ProjectiveJLine318.structureMap ℚ =
    ProjectiveJLine318.structureMap ℚ := by
  apply (JLineAtlas318.cover ℚ).hom_ext
  intro i
  fin_cases i
  · change JLineAtlas318.chart ℚ 0 ≫ (map ≫ _) = JLineAtlas318.chart ℚ 0 ≫ _
    rw [←Category.assoc,reciprocal_restriction,reciprocal_over_Q,JLineAtlas318.chart_over_base]
  · change JLineAtlas318.chart ℚ 1 ≫ (map ≫ _) = JLineAtlas318.chart ℚ 1 ≫ _
    rw [←Category.assoc,finite_restriction,finite_over_Q,JLineAtlas318.chart_over_base]

end ThreeProjectiveJMap318
