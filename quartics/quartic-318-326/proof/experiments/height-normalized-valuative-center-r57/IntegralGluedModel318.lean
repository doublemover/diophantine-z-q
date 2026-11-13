module
public import IntegralOverlapOpenImmersions318
public import GenericOpenPushout318
public section
noncomputable section
namespace IntegralGluedModel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open IntegralSourceBranches318 IntegralOverlapChartMaps318 IntegralOverlapOpenImmersions318
set_option maxHeartbeats 900000
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R : Type u) [CommRing R] (c : Fin 4 → Rˣ)
abbrev commonScheme : Scheme.{u} := Spec (CommRingCat.of (Overlap R c))
abbrev finiteScheme : Scheme.{u} := Spec (CommRingCat.of (SourceOrder R c))
abbrev infinityScheme : Scheme.{u} := Spec (CommRingCat.of (IntegralInfinityChart318.Order R c))
@[expose] def intoFinite : commonScheme R c ⟶ finiteScheme R c :=
  Spec.map (CommRingCat.ofHom (sourceMap R c).toRingHom)
@[expose] def intoInfinity : commonScheme R c ⟶ infinityScheme R c :=
  Spec.map (CommRingCat.ofHom (infinityMap R c).toRingHom)
instance intoFinite_open : IsOpenImmersion (intoFinite R c) := sourceMap_open R c
instance intoInfinity_open : IsOpenImmersion (intoInfinity R c) := infinityMap_open R c

theorem overlap_over_base :
    intoFinite R c ≫ Spec.map (CommRingCat.ofHom (algebraMap R (SourceOrder R c))) =
    intoInfinity R c ≫ Spec.map (CommRingCat.ofHom
      (algebraMap R (IntegralInfinityChart318.Order R c))) := by
  unfold intoFinite intoInfinity
  rw [←Spec.map_comp,←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact ((sourceMap R c).commutes r).trans ((infinityMap R c).commutes r).symm

/-- An actual integral scheme: glue the WHOLE original four-root affine
source to the actual integral infinity order along the proved principal overlap.
No model, gluing object, properness or regularity premise is supplied. -/
abbrev scheme : Scheme.{u} := pushout (intoFinite R c) (intoInfinity R c)
@[expose] def finiteChart : finiteScheme R c ⟶ scheme R c := pushout.inl _ _
@[expose] def infinityChart : infinityScheme R c ⟶ scheme R c := pushout.inr _ _
instance finiteChart_open : IsOpenImmersion (finiteChart R c) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (intoFinite R c) (intoInfinity R c)) WalkingSpan.left))
instance infinityChart_open : IsOpenImmersion (infinityChart R c) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (intoFinite R c) (intoInfinity R c)) WalkingSpan.right))
@[expose] def structureMap : scheme R c ⟶ Spec (CommRingCat.of R) :=
  pushout.desc (Spec.map (CommRingCat.ofHom (algebraMap R (SourceOrder R c))))
    (Spec.map (CommRingCat.ofHom (algebraMap R (IntegralInfinityChart318.Order R c))))
    (overlap_over_base R c)
@[simp] theorem finiteChart_structure : finiteChart R c ≫ structureMap R c =
    Spec.map (CommRingCat.ofHom (algebraMap R (SourceOrder R c))) := pushout.inl_desc ..
@[simp] theorem infinityChart_structure : infinityChart R c ≫ structureMap R c =
    Spec.map (CommRingCat.ofHom (algebraMap R (IntegralInfinityChart318.Order R c))) :=
  pushout.inr_desc ..

/-- Every point of this actual integral model lies in one of the two original
charts. This is coverage of the constructed scheme, not an asserted proper model. -/
theorem charts_cover (x : scheme R c) :
    (∃ a,finiteChart R c a=x) ∨ (∃ b,infinityChart R c b=x) := by
  obtain ⟨i,q,hq⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective
    (span (intoFinite R c) (intoInfinity R c)) x
  cases i with
  | none =>
    left
    refine ⟨intoFinite R c q,?_⟩
    change ((intoFinite R c) ≫ finiteChart R c) q=x
    rw [show intoFinite R c ≫ finiteChart R c =
      colimit.ι (span (intoFinite R c) (intoInfinity R c)) WalkingSpan.zero from
      colimit.w (span (intoFinite R c) (intoInfinity R c)) WalkingSpan.Hom.fst]
    exact hq
  | some j =>
    cases j with
    | left => exact Or.inl ⟨q,hq⟩
    | right => exact Or.inr ⟨q,hq⟩

/-- The same original overlap is the complete categorical intersection of
both actual charts, not merely a smaller common dense open. -/
theorem intersection_square :
    IsPullback (intoFinite R c) (intoInfinity R c) (finiteChart R c) (infinityChart R c) :=
  GenericOpenPushout318.square _ _
end IntegralGluedModel318
