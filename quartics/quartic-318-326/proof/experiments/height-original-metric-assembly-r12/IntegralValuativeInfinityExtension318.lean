module
public import IntegralValuativeOverlapPoint318
public section
noncomputable section
namespace IntegralValuativeInfinityExtension318
open Polynomial IntegralSourceBranches318 IntegralInfinityCommonBase318
open IntegralOverlapChartMaps318 IntegralValuativeOverlapPoint318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable (V K : Type*) [CommRing V] [IsDomain V] [ValuationRing V]
  [Field K] [Algebra V K] [IsFractionRing V K]
  (c : Fin 4 → Vˣ) (t : K) (y : Fin 4 → K)
  (hy : ∀ i, (y i)^2=algebraMap V K (c i : V)*(t-algebraMap V K (contacts V i)))
  (ht : ¬IsLocalization.IsInteger V t)

theorem overlap_polynomial (p : V[X]) :
    commonPoint V K c t y hy ht
      (infinityMap V c (algebraMap V[X] (IntegralInfinityChart318.Order V c) p))=
      Polynomial.aeval (algebraMap V K (c 0 : V)/y 0) p := by
  have he : ((commonPoint V K c t y hy ht).comp (infinityMap V c).toRingHom).comp
      (algebraMap V[X] (IntegralInfinityChart318.Order V c))=
      (Polynomial.aeval (algebraMap V K (c 0 : V)/y 0)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      change commonPoint V K c t y hy ht
        (infinityMap V c (algebraMap V (IntegralInfinityChart318.Order V c) a))=algebraMap V K a
      rw [AlgHom.commutes]
      exact commonPoint_constant V K c t y hy ht a
    · change commonPoint V K c t y hy ht
        (infinityMap V c (IntegralInfinityChart318.coordinate V c))= _
      rw [infinity_coordinate,commonPoint_reciprocal,Polynomial.aeval_X]
  exact RingHom.congr_fun he p

/-- Integral coefficient evaluation commutes with its original fraction-field map. -/
theorem map_eval (u : V) (p : V[X]) :
    algebraMap V K (Polynomial.eval u p)=Polynomial.aeval (algebraMap V K u) p := by
  have he : (algebraMap V K).comp (Polynomial.evalRingHom u)=
      (Polynomial.aeval (algebraMap V K u)).toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply,Polynomial.eval_C,Polynomial.aeval_C]
    · simp only [RingHom.comp_apply,Polynomial.eval_X,Polynomial.aeval_X]
  exact RingHom.congr_fun he p

/-- Equality of the entire original infinity-order field point. All three
signed roots and the complete localized coefficient base are checked. -/
theorem infinity_generic_equality (u : V) (z : Fin 3 → V)
    (hz : ∀ j, (z j)^2=Polynomial.eval u (IntegralInfinityChart318.coefficient V c j))
    (hd : IsUnit (Polynomial.eval u (IntegralInfinityChart318.denominator V c)))
    (hu : algebraMap V K u=algebraMap V K (c 0 : V)/y 0)
    (he : ∀ j, algebraMap V K (z j)=y j.succ/y 0) :
    (commonPoint V K c t y hy ht).comp (infinityMap V c).toRingHom=
      (algebraMap V K).comp (IntegralValuativeChartPoints318.infinityMap V c u z hz hd) := by
  apply ThreeRootCoordinates318.ringHom_ext
  · apply IsLocalization.ringHom_ext (Submonoid.powers (IntegralInfinityChart318.denominator V c))
    apply RingHom.ext
    intro p
    change commonPoint V K c t y hy ht
      (infinityMap V c (algebraMap (IntegralInfinityChart318.Base V c)
        (IntegralInfinityChart318.Order V c) (algebraMap V[X] (IntegralInfinityChart318.Base V c) p)))=
      algebraMap V K (IntegralValuativeChartPoints318.infinityMap V c u z hz hd
        (algebraMap (IntegralInfinityChart318.Base V c) (IntegralInfinityChart318.Order V c)
          (algebraMap V[X] (IntegralInfinityChart318.Base V c) p)))
    rw [←IsScalarTower.algebraMap_apply V[X] (IntegralInfinityChart318.Base V c)
      (IntegralInfinityChart318.Order V c),overlap_polynomial,
      IntegralValuativeChartPoints318.infinityMap_polynomial,map_eval,hu]
  · intro j
    change commonPoint V K c t y hy ht
      (infinityMap V c (IntegralOverlapRootGenerators318.infinityGenerator V c j))=
      algebraMap V K (IntegralValuativeChartPoints318.infinityMap V c u z hz hd _)
    rw [commonPoint_infinity_generator,IntegralValuativeChartPoints318.infinityMap_generator,he]

/-- The genuine integral infinity point specializes to the SAME original
whole-source field point. Equality is through the full original intersection,
not a dense-locus argument, coefficient-only equality, or root-sign choice. -/
theorem infinity_point_extension (u : V) (z : Fin 3 → V)
    (hz : ∀ j, (z j)^2=Polynomial.eval u (IntegralInfinityChart318.coefficient V c j))
    (hd : IsUnit (Polynomial.eval u (IntegralInfinityChart318.denominator V c)))
    (hu : algebraMap V K u=algebraMap V K (c 0 : V)/y 0)
    (he : ∀ j, algebraMap V K (z j)=y j.succ/y 0) :
    Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫
      IntegralValuativeChartPoints318.infinityPoint V c u z hz hd=
      IntegralValuativeGenericPoint318.point V K c t y hy := by
  have hi : Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫
      Spec.map (CommRingCat.ofHom (IntegralValuativeChartPoints318.infinityMap V c u z hz hd))=
      Spec.map (CommRingCat.ofHom (commonPoint V K c t y hy ht)) ≫ IntegralGluedModel318.intoInfinity V c := by
    unfold IntegralGluedModel318.intoInfinity
    rw [←Spec.map_comp,←Spec.map_comp]
    exact congrArg (fun f : CommRingCat.of (IntegralInfinityChart318.Order V c) ⟶ CommRingCat.of K =>
      Spec.map f) (CommRingCat.hom_ext
        (infinity_generic_equality V K c t y hy ht u z hz hd hu he).symm)
  have hf : Spec.map (CommRingCat.ofHom (commonPoint V K c t y hy ht)) ≫
      IntegralGluedModel318.intoFinite V c=
      Spec.map (CommRingCat.ofHom (IntegralValuativeGenericPoint318.sourceMap V K c t y hy)) := by
    unfold IntegralGluedModel318.intoFinite
    rw [←Spec.map_comp]
    exact congrArg (fun f : CommRingCat.of (SourceOrder V c) ⟶ CommRingCat.of K =>
      Spec.map f) (CommRingCat.hom_ext
        (RingHom.ext (commonPoint_source V K c t y hy ht)))
  unfold IntegralValuativeChartPoints318.infinityPoint IntegralValuativeGenericPoint318.point
  rw [←Category.assoc,hi,Category.assoc,
    ←show IntegralGluedModel318.intoFinite V c ≫ IntegralGluedModel318.finiteChart V c=
      IntegralGluedModel318.intoInfinity V c ≫ IntegralGluedModel318.infinityChart V c from
      CategoryTheory.Limits.pushout.condition,
    ←Category.assoc,hf]
end IntegralValuativeInfinityExtension318
