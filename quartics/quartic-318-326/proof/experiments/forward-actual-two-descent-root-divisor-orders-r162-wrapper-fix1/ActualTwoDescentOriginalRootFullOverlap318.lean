module
public import ActualTwoDescentNativeTensorRestrictionProducts318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootFullOverlap318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentRootCofactorData318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentOriginalRootIdealRestrictionComparison318
open ActualTwoDescentOriginalPuncturedCharts318 ActualTwoDescentOriginalOverlapEquivalence318
open ActualTwoDescentOriginalTwoChartCubicScheme318 ActualTwoDescentOriginalIdealOverlapValues318
open ActualTwoDescentOriginalRootOverlapRefinement318
universe u
variable {K : Type u} [Field K] [CharZero K]

lemma actual_root_chart_range (n : K) (i : Fin 3) (b : Bool) :
    (rootLocalizationMorphism n i b).opensRange=PrimeSpectrum.basicOpen (rootChartElement n i b) := by
  apply TopologicalSpace.Opens.ext
  exact PrimeSpectrum.localization_away_comap_range (RootChartRing n i b) (rootChartElement n i b)

lemma actual_overlap_affine_range (n : K) :
    (intoAffine n).opensRange=PrimeSpectrum.basicOpen (affineY n) := by
  apply TopologicalSpace.Opens.ext
  have h : Set.range (intoAffine n)=
      Set.range (Spec.map (CommRingCat.ofHom (affineOpenMap n))) := by
    ext x
    constructor
    · rintro ⟨z,rfl⟩
      exact ⟨Spec.map (originalOverlapEquiv n).toCommRingCatIso.hom z,rfl⟩
    · rintro ⟨z,rfl⟩
      refine ⟨Spec.map (originalOverlapEquiv n).toCommRingCatIso.inv z,?_⟩
      have hi : Spec.map (originalOverlapEquiv n).toCommRingCatIso.inv ≫
          Spec.map (originalOverlapEquiv n).toCommRingCatIso.hom=𝟙 _ := by
        rw [←Spec.map_comp,Iso.hom_inv_id,Spec.map_id]
      exact congrArg (fun f => Spec.map (CommRingCat.ofHom (affineOpenMap n)) (f z)) hi
  exact h.trans (PrimeSpectrum.localization_away_comap_range (AffinePuncture n) (affineY n))

/-- D(x-a) intersect D(Qa) is EXACTLY the whole original D(y).
The equality y²=(x-a)Qa covers every prime,not only rational points. -/
lemma actual_root_chart_intersection (n : K) (i : Fin 3) :
    (rootLocalizationMorphism n i false).opensRange ⊓
      (rootLocalizationMorphism n i true).opensRange=(intoAffine n).opensRange := by
  rw [actual_root_chart_range,actual_root_chart_range,actual_overlap_affine_range]
  change PrimeSpectrum.basicOpen (rootNumerator n i) ⊓ PrimeSpectrum.basicOpen (rootCofactor n i)=_
  rw [←PrimeSpectrum.basicOpen_mul,←actual_root_factorization,
    PrimeSpectrum.basicOpen_pow _ 2 (by decide)]

/-- Full intersection of the two original refined affine charts in
the SAME global cubic scheme,not merely a common dense subopen. -/
lemma actual_affine_pair_full_overlap (n : K) (i : Fin 3) :
    (rootLocalizationMorphism n i false ≫ affineChart n).opensRange ⊓
      (rootLocalizationMorphism n i true ≫ affineChart n).opensRange=(overlapEmbedding n).opensRange := by
  apply TopologicalSpace.Opens.ext
  have h : Set.range (rootLocalizationMorphism n i false) ∩
      Set.range (rootLocalizationMorphism n i true)=Set.range (intoAffine n) :=
    congrArg (fun U : (affineScheme n).Opens => (U : Set (affineScheme n)))
      (actual_root_chart_intersection n i)
  change Set.range ((affineChart n) ∘ (rootLocalizationMorphism n i false)) ∩
    Set.range ((affineChart n) ∘ (rootLocalizationMorphism n i true))=
      Set.range ((affineChart n) ∘ (intoAffine n))
  rw [Set.range_comp,Set.range_comp,Set.range_comp,
    ←Set.image_inter (affineChart n).isOpenEmbedding.injective,h]

/-- Each refined affine/infinity intersection is the SAME complete
original overlap. Both inclusion directions use original scheme maps. -/
lemma actual_affine_infinity_full_overlap (n : K) (i : Fin 3) (b : Bool) :
    (rootLocalizationMorphism n i b ≫ affineChart n).opensRange ⊓
      (infinityChart n).opensRange=(overlapEmbedding n).opensRange := by
  ext x
  change (x ∈ Set.range (rootLocalizationMorphism n i b ≫ affineChart n) ∧
    x ∈ Set.range (infinityChart n)) ↔ x ∈ Set.range (overlapEmbedding n)
  constructor
  · rintro ⟨⟨a,ha⟩,⟨z,hz⟩⟩
    have he : affineChart n (rootLocalizationMorphism n i b a)=infinityChart n z := ha.trans hz.symm
    obtain ⟨q,hq,_⟩ := GenericOpenPushout318.exists_overlap (intoAffine n) (intoInfinity n)
      (rootLocalizationMorphism n i b a) z he
    refine ⟨q,?_⟩
    change affineChart n (intoAffine n q)=x
    rw [hq]
    exact ha
  · rintro ⟨q,rfl⟩
    constructor
    · refine ⟨intoRootChart n i b q,?_⟩
      exact congrArg (fun f => f q) (actual_root_overlap_ambient n i b)
    · refine ⟨intoInfinity n q,?_⟩
      exact congrArg (fun f => f q)
        (ActualTwoDescentOriginalDegreeZeroIdealSheaf318.actual_original_overlap_square n)
end ActualTwoDescentOriginalRootFullOverlap318
