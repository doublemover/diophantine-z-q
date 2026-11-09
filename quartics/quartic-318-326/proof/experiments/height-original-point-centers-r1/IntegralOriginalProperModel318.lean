module
public import TwoChartSchemeIsomorphism318
public section
noncomputable section
namespace IntegralOriginalProperModel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralOriginalModelMorphism318
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)

/-- Injectivity uses the FULL old intersection in the new model. It cannot
be deduced from the existence of chartwise open immersions alone. -/
theorem injective : Function.Injective (map R c) := by
  intro x y h
  obtain ⟨a,rfl⟩ | ⟨b,rfl⟩ := IntegralGluedModel318.charts_cover R c x
  · obtain ⟨a',rfl⟩ | ⟨b',rfl⟩ := IntegralGluedModel318.charts_cover R c y
    · change (IntegralGluedModel318.finiteChart R c ≫ map R c) a=
        (IntegralGluedModel318.finiteChart R c ≫ map R c) a' at h
      rw [finiteChart_map] at h
      exact congrArg (IntegralGluedModel318.finiteChart R c)
        ((IntegralWholeReciprocalGluing318.originalSourceChart R c).isOpenEmbedding.injective h)
    · change (IntegralGluedModel318.finiteChart R c ≫ map R c) a=
        (IntegralGluedModel318.infinityChart R c ≫ map R c) b' at h
      rw [finiteChart_map,infinityChart_map] at h
      obtain ⟨z,hz,hz'⟩ := IntegralOriginalFullIntersection318.exists_old_overlap R c a b' h
      rw [←hz,←hz']
      exact congrArg (fun f => f z) (pushout.condition
        (f:=IntegralGluedModel318.intoFinite R c) (g:=IntegralGluedModel318.intoInfinity R c))
  · obtain ⟨a',rfl⟩ | ⟨b',rfl⟩ := IntegralGluedModel318.charts_cover R c y
    · change (IntegralGluedModel318.infinityChart R c ≫ map R c) b=
        (IntegralGluedModel318.finiteChart R c ≫ map R c) a' at h
      rw [infinityChart_map,finiteChart_map] at h
      obtain ⟨z,hz,hz'⟩ := IntegralOriginalFullIntersection318.exists_old_overlap R c a' b h.symm
      rw [←hz,←hz']
      exact congrArg (fun f => f z) (pushout.condition
        (f:=IntegralGluedModel318.intoFinite R c) (g:=IntegralGluedModel318.intoInfinity R c)).symm
    · change (IntegralGluedModel318.infinityChart R c ≫ map R c) b=
        (IntegralGluedModel318.infinityChart R c ≫ map R c) b' at h
      rw [infinityChart_map] at h
      exact congrArg (IntegralGluedModel318.infinityChart R c)
        ((IntegralOriginalInfinityEmbedding318.chart R c).isOpenEmbedding.injective h)

instance comparison_isIso : IsIso (map R c) := by
  letI : IsOpenImmersion (IntegralGluedModel318.finiteChart R c ≫ map R c) := by
    rw [finiteChart_map]
    infer_instance
  letI : IsOpenImmersion (IntegralGluedModel318.infinityChart R c ≫ map R c) := by
    rw [infinityChart_map]
    infer_instance
  exact TwoChartSchemeIsomorphism318.isIso _ _ _ (IntegralGluedModel318.charts_cover R c)
    (injective R c) (surjective R c)

/-- The ORIGINAL integral gluing, on which the global J² sections were
constructed, is isomorphic to the whole-order proper model over the same base. -/
@[expose] def comparison : IntegralGluedModel318.scheme R c ≅
    IntegralWholeReciprocalGluing318.scheme R c := asIso (map R c)

/-- Genuine properness and separatedness of the actual original integral
model, not an independently constructed projective substitute. -/
theorem proper_separated : IsProper (IntegralGluedModel318.structureMap R c) ∧
    IsSeparated (IntegralGluedModel318.structureMap R c) := by
  rw [←over_base]
  letI := (IntegralWholeProjectiveProper318.proper_separated R c).1
  letI := (IntegralWholeProjectiveProper318.proper_separated R c).2
  exact ⟨inferInstance,inferInstance⟩
end IntegralOriginalProperModel318
