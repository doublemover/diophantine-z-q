module
public import ActualTwoDescentRootCofactorData318
public import Mathlib.AlgebraicGeometry.Cover.Open
public section
noncomputable section
namespace ActualTwoDescentRootPrincipalOpenCover318
open AlgebraicGeometry ActualTwoDescentAffineChartCoordinates318
open ActualTwoDescentRootCofactorData318
variable {K : Type*} [Field K] [CharZero K]

def rootChartElement (n : K) (i : Fin 3) : Bool → AffineChart n
  | false => rootNumerator n i
  | true => rootCofactor n i

lemma actual_root_chart_span_top (n : K) (hn : n≠0) (i : Fin 3) :
    Ideal.span (Set.range (rootChartElement n i))=⊤ := by
  let J := Ideal.span (Set.range (rootChartElement n i))
  have hf : rootNumerator n i∈J := Ideal.subset_span ⟨false,rfl⟩
  have hq : rootCofactor n i∈J := Ideal.subset_span ⟨true,rfl⟩
  have hc : affineCoefficient n (rootDerivative n i)∈J := by
    rw [←actual_root_bezout]
    exact J.sub_mem hq (J.mul_mem_right _ hf)
  exact J.eq_top_of_isUnit_mem hc
    ((IsUnit.mk0 _ (actual_root_derivative_nonzero n hn i)).map (affineCoefficient n))

/-- Both actual principal opens are retained. D(Qa) contains the root;
D(x−a) contains its complement. Nonsingularity n≠0 supplies the cover. -/
def rootAffineCover (n : K) (hn : n≠0) (i : Fin 3) :
    (Spec (CommRingCat.of (AffineChart n))).OpenCover :=
  (Scheme.affineOpenCoverOfSpanRangeEqTop (R:=CommRingCat.of (AffineChart n))
    (rootChartElement n i) (actual_root_chart_span_top n hn i)).openCover

abbrev RootChartRing (n : K) (i : Fin 3) (b : Bool) :=
  Localization.Away (rootChartElement n i b)
def rootChartMap (n : K) (i : Fin 3) (b : Bool) : AffineChart n →+* RootChartRing n i b :=
  algebraMap _ _
def rootChartInverse (n : K) (i : Fin 3) (b : Bool) : RootChartRing n i b :=
  IsLocalization.Away.invSelf (rootChartElement n i b)
lemma actual_root_chart_inverse (n : K) (i : Fin 3) (b : Bool) :
    rootChartMap n i b (rootChartElement n i b)*rootChartInverse n i b=1 :=
  IsLocalization.Away.mul_invSelf _
lemma actual_root_chart_denominator_nonzero (n : K) (i : Fin 3) (b : Bool) :
    rootChartElement n i b≠0 := by
  cases b
  · exact actual_root_numerator_nonzero n i
  · exact actual_root_cofactor_nonzero n i
lemma actual_root_chart_injective (n : K) (i : Fin 3) (b : Bool) :
    Function.Injective (rootChartMap n i b) :=
  IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors
    (actual_root_chart_denominator_nonzero n i b))
end ActualTwoDescentRootPrincipalOpenCover318
