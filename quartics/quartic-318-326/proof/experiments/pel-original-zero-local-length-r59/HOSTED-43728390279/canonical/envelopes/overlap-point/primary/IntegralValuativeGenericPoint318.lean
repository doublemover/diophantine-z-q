module
public import IntegralValuativeChartPoints318
public import IntegralFullOverlapLocalization318
public import IntegralOtherRootCoordinates318
public section
noncomputable section
namespace IntegralValuativeGenericPoint318
open Polynomial IntegralSourceBranches318 IntegralRootPointMaps318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
section Algebraic
variable (V : Type u) (K : Type v) [CommRing V] [Field K] [Algebra V K]
  (c : Fin 4 → Vˣ) (t : K) (y : Fin 4 → K)
  (hy : ∀ i, (y i)^2=algebraMap V K (c i : V)*(t-algebraMap V K (contacts V i)))
@[expose] def evaluationAlgebra : Algebra V[X] K := (Polynomial.aeval t).toRingHom.toAlgebra

include hy in
theorem root_relation (i : Fin 4) :
    letI := evaluationAlgebra V K t
    (y i)^2=algebraMap V[X] K (coefficient V c i) := by
  letI := evaluationAlgebra V K t
  change (y i)^2=Polynomial.aeval t (coefficient V c i)
  simpa only [coefficient,LinearRootCoordinate318.parameter,map_mul,map_sub,
    Polynomial.aeval_C,Polynomial.aeval_X] using hy i

@[expose] def sourceMap : SourceOrder V c →+* K := by
  letI := evaluationAlgebra V K t
  exact (fourMap (coefficient V c) y (root_relation V K c t y hy)).toRingHom

theorem sourceMap_polynomial (p : V[X]) :
    sourceMap V K c t y hy (algebraMap V[X] (SourceOrder V c) p)=Polynomial.aeval t p := by
  letI := evaluationAlgebra V K t
  exact (fourMap (coefficient V c) y (root_relation V K c t y hy)).commutes p

theorem sourceMap_generator (i : Fin 4) :
    sourceMap V K c t y hy (IntegralOriginalRootCoordinates318.root V c i)=y i := by
  letI := evaluationAlgebra V K t
  exact fourMap_generator _ _ _ i

theorem sourceMap_constant (a : V) :
    sourceMap V K c t y hy (algebraMap V (SourceOrder V c) a)=algebraMap V K a := by
  rw [IsScalarTower.algebraMap_apply V V[X] (SourceOrder V c)]
  exact (sourceMap_polynomial V K c t y hy (C a)).trans (Polynomial.aeval_C t a)

/-- Equality of the entire original field point after finite extension,
not merely equality of its t coordinate or unordered root squareclasses. -/
theorem finite_generic_equality (a : V) (z : Fin 4 → V)
    (hz : ∀ i, (z i)^2=(c i : V)*(a-contacts V i))
    (ha : algebraMap V K a=t) (he : ∀ i, algebraMap V K (z i)=y i) :
    (algebraMap V K).comp (IntegralValuativeChartPoints318.finiteMap V c a z hz)=
      sourceMap V K c t y hy := by
  letI := evaluationAlgebra V K t
  apply four_ringHom_ext
  · apply Polynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply,IntegralValuativeChartPoints318.finiteMap_polynomial,
        sourceMap_polynomial,Polynomial.eval_C,Polynomial.aeval_C]
    · simp only [RingHom.comp_apply,IntegralValuativeChartPoints318.finiteMap_polynomial,
        sourceMap_polynomial,Polynomial.eval_X,Polynomial.aeval_X,ha]
  · intro i
    change algebraMap V K (IntegralValuativeChartPoints318.finiteMap V c a z hz
      (FourRootOrderSigns318.generator (coefficient V c) i))=sourceMap V K c t y hy
        (IntegralOriginalRootCoordinates318.root V c i)
    rw [IntegralValuativeChartPoints318.finiteMap_generator,sourceMap_generator,he]

end Algebraic

/- Geometric points live in the single native Scheme universe of the model.
Ring-level maps above remain independently universe-polymorphic. -/
section Geometric
variable (V K : Type u) [CommRing V] [Field K] [Algebra V K]
  (c : Fin 4 → Vˣ) (t : K) (y : Fin 4 → K)
  (hy : ∀ i, (y i)^2=algebraMap V K (c i : V)*(t-algebraMap V K (contacts V i)))
@[expose] def point : Spec (CommRingCat.of K) ⟶ IntegralGluedModel318.scheme V c :=
  Spec.map (CommRingCat.ofHom (sourceMap V K c t y hy)) ≫ IntegralGluedModel318.finiteChart V c

theorem finite_point_extension (a : V) (z : Fin 4 → V)
    (hz : ∀ i, (z i)^2=(c i : V)*(a-contacts V i))
    (ha : algebraMap V K a=t) (he : ∀ i, algebraMap V K (z i)=y i) :
    Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫
      IntegralValuativeChartPoints318.finitePoint V c a z hz=point V K c t y hy := by
  unfold IntegralValuativeChartPoints318.finitePoint point
  rw [←Category.assoc,←Spec.map_comp]
  exact congrArg (fun f : CommRingCat.of (SourceOrder V c) ⟶ CommRingCat.of K =>
    Spec.map f ≫ IntegralGluedModel318.finiteChart V c)
    (CommRingCat.hom_ext (finite_generic_equality V K c t y hy a z hz ha he))
end Geometric
end IntegralValuativeGenericPoint318
