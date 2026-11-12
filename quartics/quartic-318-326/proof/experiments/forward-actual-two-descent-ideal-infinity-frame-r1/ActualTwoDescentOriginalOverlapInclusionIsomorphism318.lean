module
public import ActualTwoDescentLocalizedTildeInclusion318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapInclusionIsomorphism318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentOriginalRootIdeals318
open ActualTwoDescentOriginalRootInfinityIdealOverlap318 ActualTwoDescentOriginalPuncturedCharts318
open ActualTwoDescentOriginalOverlapEquivalence318 ActualTwoDescentOriginalTwoChartCubicScheme318
open ActualTwoDescentOriginalRootAffineSheaf318 ActualTwoDescentLocalizedTildeInclusion318
variable {K : Type*} [Field K] [CharZero K]

instance affinePunctureMorphism_open (n : K) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom (affineOpenMap n))) :=
  IsOpenImmersion.of_isLocalization (affineY n)

lemma actual_root_ideal_affine_puncture (n : K) (i : Fin 3) :
    Ideal.map (affineOpenMap n) (rootIdeal n i)=⊤ := by
  apply Ideal.eq_top_iff_one.mpr
  have hy := Ideal.mem_map_of_mem (affineOpenMap n) (actual_affine_y_mem_root_ideal n i)
  have h := (Ideal.map (affineOpenMap n) (rootIdeal n i)).mul_mem_left (inverseY n) hy
  change inverseY n*openY n ∈ _ at h
  simpa only [mul_comm,actual_open_y_inverse] using h

lemma actual_root_affine_puncture_inclusion_isIso (n : K) (i : Fin 3) :
    IsIso ((Scheme.Modules.restrictFunctor
      (Spec.map (CommRingCat.ofHom (affineOpenMap n)))).map (rootAffineInclusion n i)) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (affineOpenMap n))) :=
    IsOpenImmersion.of_isLocalization (affineY n)
  letI := actual_tilde_inclusion_isIso (S:=AffinePuncture n)
    (Submonoid.powers (affineY n)) (rootIdeal n i) (actual_root_ideal_affine_puncture n i)
  unfold rootAffineInclusion rootIdealInclusion
  rw [Functor.map_comp]
  infer_instance

/-- Invertibility of the ACTUAL affine ideal inclusion on the entire
literal original overlap, not merely equality of ideal images. -/
lemma actual_root_overlap_inclusion_isIso (n : K) (i : Fin 3) :
    IsIso ((Scheme.Modules.restrictFunctor (intoAffine n)).map (rootAffineInclusion n i)) := by
  letI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (affineOpenMap n))) :=
    IsOpenImmersion.of_isLocalization (affineY n)
  letI := actual_root_affine_puncture_inclusion_isIso n i
  exact map_isIso_of_natIso (Scheme.Modules.restrictFunctorComp
    (Spec.map (originalOverlapEquiv n).toCommRingCatIso.hom)
    (Spec.map (CommRingCat.ofHom (affineOpenMap n)))) (rootAffineInclusion n i)
end ActualTwoDescentOriginalOverlapInclusionIsomorphism318
