module
public import ActualTwoDescentOriginalOverlapOldFrameComparison318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootOverlapRefinement318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentRootCofactorData318
open ActualTwoDescentRootPrincipalOpenCover318 ActualTwoDescentOriginalRootIdealRestrictionComparison318
open ActualTwoDescentOriginalPuncturedCharts318 ActualTwoDescentOriginalOverlapQuotientMaps318
open ActualTwoDescentOriginalOverlapLocalizationMaps318 ActualTwoDescentOriginalTwoChartCubicScheme318
open ActualTwoDescentOriginalOverlapPoleIdentity318
universe u
variable {K : Type u} [Field K] [CharZero K]

lemma actual_overlap_denominator_unit (n : K) (i : Fin 3) (b : Bool) :
    IsUnit (affineToInfinity n (rootChartElement n i b)) := by
  have h := congrArg (affineToInfinity n) (actual_root_factorization n i)
  rw [map_pow,map_mul,actual_affine_to_infinity_y] at h
  have hp : IsUnit (affineToInfinity n (rootNumerator n i)*affineToInfinity n (rootCofactor n i)) := by
    rw [←h]
    exact (actual_inverse_v_unit n).pow 2
  cases b
  · exact isUnit_of_mul_isUnit_left hp
  · exact isUnit_of_mul_isUnit_right hp

/-- Both old principal affine charts contain the ENTIRE literal
common chart; the factor maps come from their actual localizations. -/
def rootOverlapMap (n : K) (i : Fin 3) (b : Bool) : RootChartRing n i b →+* InfinityPuncture n :=
  IsLocalization.Away.lift (rootChartElement n i b) (g:=affineToInfinity n)
    (actual_overlap_denominator_unit n i b)
lemma actual_root_overlap_base (n : K) (i : Fin 3) (b : Bool) (x : AffineChart n) :
    rootOverlapMap n i b (rootChartMap n i b x)=affineToInfinity n x :=
  IsLocalization.Away.lift_eq _ _ _

def intoRootChart (n : K) (i : Fin 3) (b : Bool) : overlapScheme n ⟶
    Spec (CommRingCat.of (RootChartRing n i b)) :=
  Spec.map (CommRingCat.ofHom (rootOverlapMap n i b))
lemma actual_root_overlap_factorization (n : K) (i : Fin 3) (b : Bool) :
    intoRootChart n i b ≫ rootLocalizationMorphism n i b=intoAffine n := by
  rw [actual_into_affine]
  unfold intoRootChart rootLocalizationMorphism
  rw [←Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact actual_root_overlap_base n i b x

instance intoRootChart_open (n : K) (i : Fin 3) (b : Bool) : IsOpenImmersion (intoRootChart n i b) := by
  have h : IsOpenImmersion (intoRootChart n i b ≫ rootLocalizationMorphism n i b) := by
    rw [actual_root_overlap_factorization]
    infer_instance
  exact IsOpenImmersion.of_comp (intoRootChart n i b) (rootLocalizationMorphism n i b)

lemma actual_root_overlap_ambient (n : K) (i : Fin 3) (b : Bool) :
    intoRootChart n i b ≫ (rootLocalizationMorphism n i b ≫ affineChart n)=
      ActualTwoDescentOriginalIdealOverlapValues318.overlapEmbedding n := by
  rw [←Category.assoc,actual_root_overlap_factorization]
end ActualTwoDescentOriginalRootOverlapRefinement318
