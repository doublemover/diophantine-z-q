module
public import ActualTwoDescentAffineChartCoordinates318
public section
noncomputable section
namespace ActualTwoDescentOriginalPuncturedCharts318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentInfinityChartRing318
variable {K : Type*} [Field K] [CharZero K]

/-- The literal original affine chart with y inverted, and the literal
infinity chart with v inverted. No replacement rational-function model. -/
abbrev AffinePuncture (n : K) := Localization.Away (affineY n)
abbrev InfinityPuncture (n : K) := Localization.Away (chartV n)
def affineOpenMap (n : K) : AffineChart n →+* AffinePuncture n := algebraMap _ _
def infinityOpenMap (n : K) : InfinityChart n →+* InfinityPuncture n := algebraMap _ _
def openX (n : K) := affineOpenMap n (affineX n)
def openY (n : K) := affineOpenMap n (affineY n)
def inverseY (n : K) : AffinePuncture n := IsLocalization.Away.invSelf (affineY n)
def openU (n : K) := infinityOpenMap n (chartU n)
def openV (n : K) := infinityOpenMap n (chartV n)
def inverseV (n : K) : InfinityPuncture n := IsLocalization.Away.invSelf (chartV n)
def affineOpenCoefficient (n : K) := (affineOpenMap n).comp (affineCoefficient n)
def infinityOpenCoefficient (n : K) := (infinityOpenMap n).comp (chartCoefficient n)

@[simp] lemma actual_open_y_inverse (n : K) : openY n*inverseY n=1 :=
  IsLocalization.Away.mul_invSelf (affineY n)
@[simp] lemma actual_open_v_inverse (n : K) : openV n*inverseV n=1 :=
  IsLocalization.Away.mul_invSelf (chartV n)

lemma actual_open_affine_cubic (n : K) :
    openY n^2-openX n^3-2*affineOpenCoefficient n n*openX n^2+
      3*(affineOpenCoefficient n n)^2*openX n=0 := by
  have h := congrArg (affineOpenMap n) (actual_affine_cubic n)
  simpa only [map_sub,map_add,map_mul,map_pow,map_ofNat,map_zero] using h

lemma actual_open_infinity_cubic (n : K) :
    openV n-openU n^3-2*infinityOpenCoefficient n n*openU n^2*openV n+
      3*(infinityOpenCoefficient n n)^2*openU n*openV n^2=0 := by
  have h := congrArg (infinityOpenMap n) (actual_chart_cubic_relation n)
  unfold chartFactor at h
  simp only [map_sub,map_add,map_mul,map_pow,map_ofNat] at h
  change openV n*(1-2*infinityOpenCoefficient n n*openU n^2+
    3*(infinityOpenCoefficient n n)^2*openU n*openV n)=openU n^3 at h
  linear_combination h
end ActualTwoDescentOriginalPuncturedCharts318
