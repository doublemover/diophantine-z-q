module
public import ThreeJLaurentDifferentialJoin318
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public section
noncomputable section
namespace ThreeJGlobalRamificationScheme318
open AlgebraicGeometry CategoryTheory Polynomial
open ThreeJRamificationIdealCharts318
open ThreeJCuspDifferentialCharts318 ThreeProjectiveJCertificates318
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The nonreduced degree-six algebra defined by the complete finite-chart
ramification equation, including the finite cusp with multiplicity two. -/
abbrev Ring := AdjoinRoot finiteEquation
instance ring_finite : Module.Finite ℚ Ring := finiteEquation_monic.finite_adjoinRoot
instance ring_free : Module.Free ℚ Ring := finiteEquation_monic.free_adjoinRoot
theorem rank_six : Module.finrank ℚ Ring=6 := by
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasis' finiteEquation_monic).basis,
    Fintype.card_fin]
  exact finiteEquation_degree

abbrev Source := Spec (CommRingCat.of Ring)
@[expose] def finiteInclusion : Source ⟶ Spec (CommRingCat.of ℚ[X]) :=
  Spec.map (CommRingCat.ofHom (AdjoinRoot.mk finiteEquation))
instance finiteInclusion_closed : IsClosedImmersion finiteInclusion :=
  IsClosedImmersion.spec_of_surjective _ AdjoinRoot.mk_surjective
@[expose] def embedding : Source ⟶ ProjectiveJLine318.scheme ℚ :=
  finiteInclusion ≫ JLineAtlas318.chart ℚ 1
@[expose] def structureMap : Source ⟶ Spec (CommRingCat.of ℚ) := Spec.algebraMap ℚ Ring
instance structure_finite : IsFinite structureMap := by
  exact (IsFinite.SpecMap_iff _).mpr (RingHom.finite_algebraMap.mpr inferInstance)

theorem over_Q : embedding ≫ ProjectiveJLine318.structureMap ℚ=structureMap := by
  rw [embedding,Category.assoc,JLineAtlas318.chart_over_base,finiteInclusion,←Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  ext q
  rfl

instance embedding_proper : IsProper embedding := by
  letI : IsProper (embedding ≫ ProjectiveJLine318.structureMap ℚ) := by
    rw [over_Q]
    infer_instance
  exact IsProper.of_comp _ (ProjectiveJLine318.structureMap ℚ)

/-- The full degree-six scheme is genuinely closed in the original
projective source. Properness, not a closed-point count, closes the affine
embedding and prevents an unproved extension at infinity. -/
instance embedding_closed : IsClosedImmersion embedding := by
  letI : IsPreimmersion embedding := by unfold embedding; infer_instance
  exact IsClosedImmersion.of_isPreimmersion embedding embedding.isClosedMap.isClosed_range

/-- A global ideal-sheaf datum on the original projective source,
constructed from the actual closed immersion. Identification with a global
relative differential sheaf is a separate comparison, not a definition. -/
@[expose] def ideal : (ProjectiveJLine318.scheme ℚ).IdealSheafData := embedding.ker

theorem support_eq_range : (ideal.support : Set (ProjectiveJLine318.scheme ℚ))=
    Set.range embedding := by
  rw [ideal,Scheme.Hom.support_ker]
  exact embedding.isClosedMap.isClosed_range.closure_eq

/-- The global object has no extra source point outside the actual finite
projective chart; in particular it does not add a spurious infinity component. -/
theorem support_in_finite_chart :
    (ideal.support : Set (ProjectiveJLine318.scheme ℚ)) ⊆ Set.range (JLineAtlas318.chart ℚ 1) := by
  rw [support_eq_range]
  rintro _ ⟨x,rfl⟩
  exact ⟨finiteInclusion x,rfl⟩

/-- Exact defining ideal of the original affine immersion, with all
nilpotent structure retained. Together with the full-overlap ideal equality,
this records the actual two-chart descent equation for the global candidate. -/
theorem finite_kernel : RingHom.ker (AdjoinRoot.mk finiteEquation)=Ideal.span {finiteEquation} := by
  ext q
  simp only [RingHom.mem_ker,AdjoinRoot.mk_eq_zero,Ideal.mem_span_singleton]

lemma numerator_contains_of_denominator_mem (f g : ℚ[X]) (hc : IsCoprime f g)
    (p : PrimeSpectrum ℚ[X]) (hg : g ∈ p.asIdeal) :
    p ∈ (RationalPairLocalMaps318.numeratorBase f).opensRange := by
  have hp : p ∈ PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g := by
    rw [ThreeProjectiveJCertificates318.basicOpen_cover_of_coprime hc]
    trivial
  have hf : p ∈ PrimeSpectrum.basicOpen f := hp.resolve_right (fun h => h hg)
  have he : (RationalPairLocalMaps318.numeratorBase f).opensRange=PrimeSpectrum.basicOpen f := by
    apply TopologicalSpace.Opens.ext
    exact PrimeSpectrum.localization_away_comap_range _ _
  rwa [he]

/-- The monic Laurent presentation and both reciprocal-target cusp
presentations cover every source scheme prime, not only the four analytic
ramification points or the two rational cusps. -/
theorem every_source_point (p : ProjectiveJLine318.scheme ℚ) :
    p ∈ ProjectiveLineOverlap318.embedding.opensRange ∨
      p ∈ ThreeJCuspDifferentialCharts318.finiteEmbedding.opensRange ∨
      p ∈ ThreeJCuspDifferentialCharts318.infinityEmbedding.opensRange := by
  obtain ⟨i,q,hq⟩ := ThreeProjectiveJMap318.sourceCover.exists_eq p
  subst p
  by_cases hx : (X:ℚ[X]) ∈ q.asIdeal
  · fin_cases i
    · have hn := numerator_contains_of_denominator_mem reciprocalNumerator reciprocalDenominator
        reciprocal_coprime q hx
      obtain ⟨z,hz⟩ := hn
      right; right
      refine ⟨z,?_⟩
      change JLineAtlas318.chart ℚ 0 (RationalPairLocalMaps318.numeratorBase reciprocalNumerator z)=_
      rw [hz]
      rfl
    · have hg : finiteDenominator ∈ q.asIdeal := by
        change ((X : ℚ[X])^3) ∈ (q.asIdeal : Ideal ℚ[X])
        exact Ideal.pow_mem_of_mem (q.asIdeal : Ideal ℚ[X]) hx 3 (by decide)
      have hn := numerator_contains_of_denominator_mem finiteNumerator finiteDenominator finite_coprime q hg
      obtain ⟨z,hz⟩ := hn
      right; left
      refine ⟨z,?_⟩
      change JLineAtlas318.chart ℚ 1 (RationalPairLocalMaps318.numeratorBase finiteNumerator z)=_
      rw [hz]
      rfl
  · exact Or.inl (ProjectiveLineLaurentComplement318.chart_mem_laurent i q hx)

end ThreeJGlobalRamificationScheme318
