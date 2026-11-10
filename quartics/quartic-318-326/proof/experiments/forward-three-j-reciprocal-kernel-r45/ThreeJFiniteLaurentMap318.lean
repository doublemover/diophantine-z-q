module
public import ThreeJLaurentEquiv318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.LinearAlgebra.Dimension.Localization
public section
noncomputable section
namespace ThreeJFiniteLaurentMap318
open AlgebraicGeometry CategoryTheory Polynomial
open ThreeJMonicAlgebra318 ThreeJLaurentEquiv318
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- This scalar structure is the exact j-coordinate pullback, not the
pre-existing T-coordinate scalar structure on the same Laurent ring. -/
@[expose,instance_reducible] def jAlgebra : Algebra Base Laurent := baseMap.toRingHom.toAlgebra

@[expose] def baseCoordinateEquiv :
    letI := jAlgebra
    letI : Module Base Laurent := jAlgebra.toModule
    Model ≃ₐ[Base] Laurent := by
  letI := jAlgebra
  letI : Module Base Laurent := jAlgebra.toModule
  exact { coordinateEquiv.toRingEquiv with commutes' := coordinate_base }

lemma laurent_finite_free :
    letI := jAlgebra
    letI : Module Base Laurent := jAlgebra.toModule
    Module.Finite Base Laurent ∧ Module.Free Base Laurent := by
  letI := jAlgebra
  letI : Module Base Laurent := jAlgebra.toModule
  exact ⟨Module.Finite.equiv baseCoordinateEquiv.toLinearEquiv,
    Module.Free.of_equiv baseCoordinateEquiv.toLinearEquiv⟩

lemma laurent_rank_four :
    letI := jAlgebra
    letI : Module Base Laurent := jAlgebra.toModule
    Module.finrank Base Laurent=4 := by
  letI := jAlgebra
  letI : Module Base Laurent := jAlgebra.toModule
  exact baseCoordinateEquiv.toLinearEquiv.finrank_eq.symm.trans rank_four

/-- The actual finite-target affine map on the original punctured projective
source chart, carrying the j pullback, is scheme-theoretically finite. -/
@[expose] def finiteTargetMap : Spec (CommRingCat.of Laurent) ⟶ Spec (CommRingCat.of Base) :=
  Spec.map (CommRingCat.ofHom baseMap.toRingHom)

instance finiteTargetMap_finite : IsFinite finiteTargetMap := by
  letI := jAlgebra
  letI : Module Base Laurent := jAlgebra.toModule
  letI : Module.Finite Base Laurent := laurent_finite_free.1
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

/-- Exact scheme-level comparison with the existing global j morphism on
the original Laurent source inclusion and original finite target chart. -/
theorem original_scheme_square :
    ProjectiveLineOverlap318.embedding ≫ ThreeProjectiveJMap318.map =
      finiteTargetMap ≫ JLineAtlas318.chart ℚ 1 := by
  unfold ProjectiveLineOverlap318.embedding
  rw [Category.assoc,ThreeProjectiveJMap318.finite_restriction]
  change Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] Laurent)) ≫
    ThreeAffineJMaps318.finiteMap = _
  rw [←ThreeProjectiveJMap318.evaluation_t]
  unfold ThreeAffineJMaps318.finiteMap
  rw [RationalPairDenominatorEvaluation318.evaluation_formula _ _ _
    (Polynomial.aeval (R:=ℚ) ProjectiveLineOverlap318.t)
    (ProjectiveLineOverlap318.s^3) ThreeProjectiveJMap318.finite_denominator_inverse]
  have he : Polynomial.aeval (R:=ℚ) ProjectiveLineOverlap318.t
      ThreeProjectiveJCertificates318.finiteNumerator * ProjectiveLineOverlap318.s^3=jLaurent := by
    simp only [ThreeProjectiveJCertificates318.finiteNumerator,map_mul,map_add,map_pow,
      map_ofNat,Polynomial.aeval_X,jLaurent]
  rw [he]
  rfl

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- The compatible fraction fields of the explicit j-algebra have degree4.
The preceding Laurent equivalence and scheme square identify its rational
source and exact j pullback; comparison with generic stalks is separate. -/
theorem fraction_degree_four :
    Module.finrank (FractionRing Base) (FractionRing Model)=4 := by
  rw [IsFractionRing.finrank_eq Base (FractionRing Base) Model (FractionRing Model)]
  exact rank_four

/-- The base fraction-field scalar action sends the original j generator to
the fraction of the same j in the quartic/Laurent presentation. -/
lemma fraction_scalar_j :
    algebraMap (FractionRing Base) (FractionRing Model)
      (algebraMap Base (FractionRing Base) X)=algebraMap Model (FractionRing Model) j := by
  rw [←IsScalarTower.algebraMap_apply Base (FractionRing Base),
    IsScalarTower.algebraMap_apply Base Model]
  rfl

end ThreeJFiniteLaurentMap318
