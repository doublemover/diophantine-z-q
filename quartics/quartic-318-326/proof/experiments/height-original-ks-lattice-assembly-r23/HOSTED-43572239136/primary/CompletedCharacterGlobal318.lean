module
public import CompletedCharacterSchemeMaps318
public import ContactGlobalSmooth318
public import Mathlib.AlgebraicGeometry.Gluing
public section
noncomputable section
namespace CompletedCharacterGlobal318
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SourceTwistArithmetic318
open CompletedCharacterSchemeMaps318
set_option maxHeartbeats 500000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Compatibility on a specified actual pullback implies the canonical
pullback compatibility required by the open-cover gluing theorem. -/
lemma compatibility_of_actual_pullback {P X Y Z T : Scheme}
    {a : P⟶X} {b : P⟶Y} {f : X⟶Z} {g : Y⟶Z}
    (h : IsPullback a b f g) (F : X⟶T) (G : Y⟶T)
    (hab : a≫F=b≫G) : pullback.fst f g≫F=pullback.snd f g≫G := by
  apply (cancel_epi h.isoPullback.hom).mp
  simpa only [←Category.assoc,h.isoPullback_hom_fst,h.isoPullback_hom_snd] using hab

lemma diagonal_compatibility {X Z T : Scheme} (f : X⟶Z) [Mono f] (F : X⟶T) :
    pullback.fst f f≫F=pullback.snd f f≫F := by
  have h : pullback.fst f f=pullback.snd f f :=
    (cancel_mono f).mp pullback.condition
  rw [h]

@[expose] def localMap (i:Fin 4) : (b:Bool)→(ContactGlobalSmooth318.cover units).X b⟶Target i
  | false=>finiteChartMap i
  | true=>infinityChartMap i

theorem compatible (i:Fin 4) (b d:Bool) :
    pullback.fst ((ContactGlobalSmooth318.cover units).f b)
      ((ContactGlobalSmooth318.cover units).f d)≫localMap i b=
    pullback.snd _ _≫localMap i d := by
  cases b <;> cases d
  · exact diagonal_compatibility (SourceGlobalAffine318.chartEmbedding units) (finiteChartMap i)
  · exact compatibility_of_actual_pullback (ContactFullOverlap318.actual_pullback units)
      (finiteChartMap i) (infinityChartMap i) (maps_agree i)
  · exact compatibility_of_actual_pullback (ContactFullOverlap318.actual_pullback units).flip
      (infinityChartMap i) (finiteChartMap i) (maps_agree i).symm
  · exact diagonal_compatibility (InfinityGlobalScheme318.chartEmbedding units) (infinityChartMap i)

/-- The existing finite source-character map extends to the literal completed
published short Weierstrass scheme, on the whole actual contact normalization. -/
@[expose] def completedMap (i:Fin 4) : ContactGlobalSmooth318.Model units⟶Target i :=
  (ContactGlobalSmooth318.cover units).glueMorphisms (localMap i) (compatible i)

theorem on_finite (i:Fin 4) :
    SourceGlobalAffine318.chartEmbedding units≫completedMap i=finiteChartMap i :=
  (ContactGlobalSmooth318.cover units).ι_glueMorphisms (localMap i) (compatible i) false

theorem on_infinity (i:Fin 4) :
    InfinityGlobalScheme318.chartEmbedding units≫completedMap i=infinityChartMap i :=
  (ContactGlobalSmooth318.cover units).ι_glueMorphisms (localMap i) (compatible i) true

/-- The completed map has the actual original Q-structure square. -/
theorem over_Q (i:Fin 4) :
    completedMap i≫WeierstrassGluing318.structureMap (publishedA i) (publishedB i)=
    (ContactProjectiveModel318.coverMap units).fromNormalization≫ProjectiveJLine318.structureMap ℚ := by
  apply (ContactGlobalSmooth318.cover units).hom_ext
  intro b
  cases b
  · change SourceGlobalAffine318.chartEmbedding units≫completedMap i≫_=_
    rw [←Category.assoc,on_finite,finite_over_Q]
    exact (SourceGlobalAffine318.chartEmbedding_over_Q units).symm
  · change InfinityGlobalScheme318.chartEmbedding units≫completedMap i≫_=_
    rw [←Category.assoc,on_infinity,infinity_over_Q]
    exact (InfinityStructureSmooth318.chartEmbedding_over_Q units).symm

/-- Any extension agreeing on both complete actual charts is this map. -/
theorem unique (i:Fin 4) (f:ContactGlobalSmooth318.Model units⟶Target i)
    (hf:SourceGlobalAffine318.chartEmbedding units≫f=finiteChartMap i)
    (hi:InfinityGlobalScheme318.chartEmbedding units≫f=infinityChartMap i) :
    f=completedMap i := by
  apply (ContactGlobalSmooth318.cover units).hom_ext
  intro b
  cases b
  · exact hf.trans (on_finite i).symm
  · exact hi.trans (on_infinity i).symm
end CompletedCharacterGlobal318
