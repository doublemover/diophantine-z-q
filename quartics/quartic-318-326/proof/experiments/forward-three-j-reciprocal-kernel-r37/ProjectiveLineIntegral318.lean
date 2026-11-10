module
public import ThreeRationalModuliScheme318
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Topology.Irreducible
public section
noncomputable section
namespace ProjectiveLineIntegral318
open AlgebraicGeometry CategoryTheory Polynomial TopologicalSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

instance laurent_domain : IsDomain ThreeJLaurentEquiv318.Laurent :=
  Localization.Away.isDomain (Polynomial.X_ne_zero : (Polynomial.X:Polynomial ℚ) ≠ 0)

/-- Every nonempty scheme open meets the actual Laurent chart. The proof
uses all original affine charts and their actual prime-spectrum overlap. -/
theorem laurent_dense : DenseRange ProjectiveLineOverlap318.embedding := by
  apply dense_iff_inter_open.mpr
  intro U hU hne
  obtain ⟨p,hp⟩ := hne
  obtain ⟨i,q,hq⟩ := ThreeProjectiveJMap318.sourceCover.exists_eq p
  have hqU : q ∈ JLineAtlas318.chart ℚ i ⁻¹' U := by
    change JLineAtlas318.chart ℚ i q ∈ U
    rw [hq]
    exact hp
  have hbasic : (PrimeSpectrum.basicOpen (Polynomial.X:Polynomial ℚ) :
      Set (PrimeSpectrum (Polynomial ℚ))).Nonempty := by
    refine ⟨⟨⊥,Ideal.isPrime_bot⟩,?_⟩
    change (Polynomial.X:Polynomial ℚ) ≠ 0
    exact Polynomial.X_ne_zero
  obtain ⟨r,hrU,hrX⟩ := nonempty_preirreducible_inter
    (hU.preimage (JLineAtlas318.chart ℚ i).continuous)
    (PrimeSpectrum.basicOpen (Polynomial.X:Polynomial ℚ)).isOpen ⟨q,hqU⟩ hbasic
  exact ⟨JLineAtlas318.chart ℚ i r,hrU,
    ProjectiveLineLaurentComplement318.chart_mem_laurent i r hrX⟩

instance projective_irreducible : IrreducibleSpace (ProjectiveJLine318.scheme ℚ) := by
  apply (irreducibleSpace_def _).mpr
  have h : IsIrreducible (Set.range ProjectiveLineOverlap318.embedding) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ
        (Spec (CommRingCat.of ThreeJLaurentEquiv318.Laurent))).image
          ProjectiveLineOverlap318.embedding ProjectiveLineOverlap318.embedding.continuous.continuousOn
  change IsIrreducible (Set.univ : Set (ProjectiveJLine318.scheme ℚ))
  simpa only [laurent_dense.closure_range] using h.closure
instance projective_reduced : IsReduced (ProjectiveJLine318.scheme ℚ) :=
  IsReduced.of_openCover _ ThreeProjectiveJMap318.sourceCover
instance projective_integral : IsIntegral (ProjectiveJLine318.scheme ℚ) :=
  isIntegral_of_irreducibleSpace_of_isReduced _

instance laurent_dominant : IsDominant ProjectiveLineOverlap318.embedding := ⟨laurent_dense⟩
instance chart_dominant (i : Fin 2) : IsDominant (JLineAtlas318.chart ℚ i) :=
  ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (JLineAtlas318.chart ℚ i).isOpenEmbedding.isOpenMap⟩

end ProjectiveLineIntegral318
