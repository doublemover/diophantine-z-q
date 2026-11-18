module
public import IntegralOriginalModelMorphism318
public section
noncomputable section
namespace IntegralOriginalFullIntersection318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralSourceBranches318 IntegralInfinityCommonBase318 IntegralInfinityOverlapRealization318
open IntegralOverlapChartMaps318
open scoped TensorProduct
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v

/-- Transport the open range with both immersion witnesses in scope, so no
rewriting motive retains a witness for the old morphism. -/
private theorem opensRange_eq_of_eq {X Y : Scheme.{v}} {f g : X ⟶ Y}
    [IsOpenImmersion f] [IsOpenImmersion g] (heq : f = g) :
    f.opensRange = g.opensRange := by
  subst g
  rfl

variable (R : Type*) [CommRing R] (c : Fin 4 → Rˣ)
local instance infinityAlgebra : Algebra (IntegralInfinityChart318.Base R c) (CommonBase R c) :=
  (infinityBaseMap R c).toRingHom.toAlgebra

/-- Capture the same native commutative-ring dictionaries as the already
proved infinity open immersion before elaborating includeRight. -/
local instance infinityCommRing : CommRing (IntegralInfinityChart318.Order R c) := inferInstance
local instance infinityOverlapCommRing : CommRing
    (CommonBase R c ⊗[IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c) :=
  inferInstance

/-- The OLD infinity overlap is exactly its coordinate principal open on
all prime ideals, not merely an open set containing the generic point. -/
theorem infinity_range : (IntegralGluedModel318.intoInfinity R c).opensRange=
    PrimeSpectrum.basicOpen (IntegralInfinityChart318.coordinate R c) := by
  letI := rightAlgebra (IntegralInfinityChart318.Base R c) (CommonBase R c)
    (IntegralInfinityChart318.Order R c)
  letI := infinityOrder_localization R c
  letI := IntegralOverlapOpenImmersions318.infinity_right_open R c
  have he : IntegralGluedModel318.intoInfinity R c =
      Spec.map (actualOverlapEquiv R c).symm.toRingEquiv.toCommRingCatIso.hom ≫
      Spec.map (CommRingCat.ofHom
        (show IntegralInfinityChart318.Order R c →+*
          (CommonBase R c ⊗[IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c) from
          (Algebra.TensorProduct.includeRight : IntegralInfinityChart318.Order R c
            →ₐ[IntegralInfinityChart318.Base R c]
              CommonBase R c ⊗[IntegralInfinityChart318.Base R c]
                IntegralInfinityChart318.Order R c).toRingHom)) := by
    rw [←Spec.map_comp]
    rfl
  refine (opensRange_eq_of_eq he).trans ?_
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range
    (CommonBase R c ⊗[IntegralInfinityChart318.Base R c] IntegralInfinityChart318.Order R c)
    (IntegralInfinityChart318.coordinate R c)

/-- An original finite point and an original infinity point meeting in the
whole proper model already meet through the SAME original old overlap. -/
theorem exists_old_overlap
    (a : IntegralGluedModel318.finiteScheme R c)
    (b : IntegralGluedModel318.infinityScheme R c)
    (h : IntegralWholeReciprocalGluing318.originalSourceChart R c a=
      IntegralOriginalInfinityEmbedding318.chart R c b) :
    ∃ z,IntegralGluedModel318.intoFinite R c z=a ∧
      IntegralGluedModel318.intoInfinity R c z=b := by
  let e := Spec.map (IntegralWholeFiniteComparison318.comparison R c).symm.toRingEquiv.toCommRingCatIso.hom
  obtain ⟨q,hqf,hqi⟩ := GenericOpenPushout318.exists_overlap
    (IntegralWholeReciprocalGluing318.intoFinite R c)
    (IntegralWholeReciprocalGluing318.intoInfinity R c)
    (e a) (IntegralOriginalInfinityEmbedding318.inclusion R c b) h
  have hb : IntegralOriginalInfinityEmbedding318.inclusion R c b ∈
      (IntegralWholeReciprocalGluing318.intoInfinity R c).opensRange := ⟨q,hqi⟩
  change IntegralOriginalInfinityEmbedding318.inclusion R c b ∈
    (Spec.map (CommRingCat.ofHom (IntegralWholeOrderOpenMaps318.infinityMap R c))).opensRange at hb
  rw [IntegralWholeOpenRanges318.infinity_range] at hb
  change ¬ IntegralOriginalInfinityEmbedding318.ringMap R c
    (algebraMap (Polynomial R) (IntegralWholeReciprocalOrders318.InfinityOrder R c)
      Polynomial.X) ∈ b.asIdeal at hb
  rw [IntegralOriginalInfinityEmbedding318.polynomial] at hb
  have hb' : b ∈ (IntegralGluedModel318.intoInfinity R c).opensRange := by
    rw [infinity_range]
    exact hb
  obtain ⟨z,hz⟩ := hb'
  refine ⟨z,?_,hz⟩
  apply (IntegralWholeReciprocalGluing318.originalSourceChart R c).isOpenEmbedding.injective
  calc
    _ = IntegralOriginalInfinityEmbedding318.chart R c
        (IntegralGluedModel318.intoInfinity R c z) :=
      congrArg (fun f => f z) (IntegralOriginalGluingCompatibility318.chart_agreement R c)
    _ = _ := by rw [hz];exact h.symm
end IntegralOriginalFullIntersection318
