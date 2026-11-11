module
public import PELOriginalAdditionChartMorphism318
public import PELOriginalProductComplexPoints318
public section
noncomputable section
namespace PELOriginalAdditionSchemeMorphism318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits QuaternionicRealPeriod318
open DiscreteComplexPeriodAtlas318 PELOriginalPolarizationTransitions318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318
open PELOriginalProductChartCover318 PELOriginalProductComplexPoints318
open PELOriginalReducedProjectiveCandidate318 PELOriginalCandidateComplexPoints318
variable (τ : ℂ) (hτ : 0<τ.im)

lemma projection_add (z a : ComplexVectors) :
    projection (P τ) (z+a)=projection (P τ) z+projection (P τ) a :=
  map_add (QuotientAddGroup.mk' (P τ)) z a

/-- Genuine equality on the full scheme overlap of two ACTUAL tensor
charts. Original pair injectivity identifies the true source torus
points, and reduced finite-type scheme comparison then proves equality
of the regular morphisms, not just their selected complex values. -/
theorem compatible (rs st : Label 3 × Label 3) :
    pullback.fst (chartInclusion τ hτ rs) (chartInclusion τ hτ st)≫
      PELOriginalAdditionChartMorphism318.morphism τ hτ rs.1 rs.2=
    pullback.snd (chartInclusion τ hτ rs) (chartInclusion τ hτ st)≫
      PELOriginalAdditionChartMorphism318.morphism τ hτ st.1 st.2 := by
  let a := chartInclusion τ hτ rs
  let b := chartInclusion τ hτ st
  let ρ := (pullback.fst a b≫a)≫baseMap τ hτ
  letI : IsReduced (pullback a b) := isReduced_of_isOpenImmersion (pullback.fst a b≫a)
  letI : LocallyOfFiniteType ρ := by dsimp [ρ,a,b]; infer_instance
  have hs : (pullback.fst a b≫PELOriginalAdditionChartMorphism318.morphism τ hτ rs.1 rs.2)≫
      π τ hτ=ρ := by
    rw [Category.assoc,PELOriginalAdditionChartMorphism318.over_complex]
    dsimp [ρ,a]
    rw [Category.assoc,chart_over]
    rfl
  have ht : (pullback.snd a b≫PELOriginalAdditionChartMorphism318.morphism τ hτ st.1 st.2)≫
      π τ hτ=ρ := by
    rw [Category.assoc,PELOriginalAdditionChartMorphism318.over_complex]
    change pullback.snd a b≫Spec.map (CommRingCat.ofHom
      (algebraMap ℂ (PELOriginalProductChartPoints318.ProductRing τ hτ st.1 st.2)))=_
    rw [←chart_over,←Category.assoc]
    exact congrArg (fun h => h≫baseMap τ hτ) (pullback.condition (f := a) (g := b)).symm
  apply ReducedComplexPointMorphisms318.ext ρ (π τ hτ) _ _ hs ht
  intro p hp
  have hps : (p≫pullback.fst a b)≫AffineComplexProjectiveVector318.structureMap=𝟙 _ := by
    change (p≫pullback.fst a b)≫Spec.map (CommRingCat.ofHom (algebraMap ℂ _))=𝟙 _
    rw [←chart_over,Category.assoc,←Category.assoc (pullback.fst a b)]
    exact hp
  have hpt : (p≫pullback.snd a b)≫AffineComplexProjectiveVector318.structureMap=𝟙 _ := by
    change (p≫pullback.snd a b)≫Spec.map (CommRingCat.ofHom (algebraMap ℂ _))=𝟙 _
    rw [←chart_over,Category.assoc,←Category.assoc (pullback.snd a b),←pullback.condition]
    exact hp
  obtain ⟨z,u,hz,hu,hzu⟩ := PELOriginalAdditionChartMorphism318.every_point τ hτ rs.1 rs.2
    (p≫pullback.fst a b) hps
  obtain ⟨w,v,hw,hv,hwv⟩ := PELOriginalAdditionChartMorphism318.every_point τ hτ st.1 st.2
    (p≫pullback.snd a b) hpt
  have he : pair τ hτ (projection (P τ) z) (projection (P τ) u)=
      pair τ hτ (projection (P τ) w) (projection (P τ) v) := by
    rw [←chart_pair τ hτ rs.1 rs.2 z u hz hu,←chart_pair τ hτ st.1 st.2 w v hw hv,
      ←hzu,←hwv]
    simp only [Category.assoc,pullback.condition_assoc]
  have hpairs := pair_injective τ hτ he
  have hsum : projection (P τ) (z+u)=projection (P τ) (w+v) := by
    rw [projection_add,projection_add,congrArg Prod.fst hpairs,congrArg Prod.snd hpairs]
  rw [←Category.assoc,←Category.assoc,hzu,hwv,
    PELOriginalAdditionChartMorphism318.original_point_action,
    PELOriginalAdditionChartMorphism318.original_point_action,hsum]

/-- Genuine regular binary addition on the SAME original algebraic
candidate and its ACTUAL product over C. Construction proceeds through
regular section coordinates and scheme gluing, rather than transporting
a set-level or analytic group operation across a point bijection. -/
@[expose] def addition : Product τ hτ ⟶ candidate τ hτ :=
  (affineCover τ hτ).glueMorphisms
    (fun rs => PELOriginalAdditionChartMorphism318.morphism τ hτ rs.1 rs.2) (compatible τ hτ)

@[reassoc] theorem chart_addition (j k : Label 3) :
    chartInclusion τ hτ (j,k)≫addition τ hτ=PELOriginalAdditionChartMorphism318.morphism τ hτ j k :=
  (affineCover τ hτ).ι_glueMorphisms _ _ (j,k)

@[reassoc] theorem over_complex : addition τ hτ≫π τ hτ=baseMap τ hτ := by
  apply (affineCover τ hτ).hom_ext
  intro rs
  rw [←Category.assoc,chart_addition,PELOriginalAdditionChartMorphism318.over_complex,chart_over]
  rfl

/-- Exact original source-cover addition square. -/
theorem original_point_action (z a : ComplexVectors) :
    pair τ hτ (projection (P τ) z) (projection (P τ) a)≫addition τ hτ=
      candidateComplexPoint τ hτ (projection (P τ) (z+a)) := by
  obtain ⟨j,hj⟩ := PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ z
  obtain ⟨k,hk⟩ := PELOriginalChartSchemePointIdentity318.cover_nonzero τ hτ a
  rw [←chart_pair τ hτ j k z a hj hk,Category.assoc,chart_addition]
  exact PELOriginalAdditionChartMorphism318.original_point_action τ hτ j k z a hj hk

/-- The entire original analytic torus addition, now literally realized
by the constructed regular binary scheme morphism. -/
theorem pair_action (q r : Base τ) :
    pair τ hτ q r≫addition τ hτ=candidateComplexPoint τ hτ (q+r) := by
  obtain ⟨z,rfl⟩ := quotient_surjective (P τ) q
  obtain ⟨a,rfl⟩ := quotient_surjective (P τ) r
  rw [original_point_action,projection_add]
end PELOriginalAdditionSchemeMorphism318
