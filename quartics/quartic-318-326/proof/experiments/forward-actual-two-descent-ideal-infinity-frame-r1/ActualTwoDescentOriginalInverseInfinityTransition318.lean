module
public import ActualTwoDescentOriginalRootAffineSheaf318
public import ClutchedModule318
public section
noncomputable section
namespace ActualTwoDescentOriginalInverseInfinityTransition318
open CategoryTheory AlgebraicGeometry
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityGlobalFactorUnit318
open ActualTwoDescentOriginalPuncturedCharts318 ActualTwoDescentOriginalTwoChartCubicScheme318
variable {K : Type*} [Field K] [CharZero K]

/-- Actual inverse of u in the literal common chart: v=e*u³ and v is
inverted there, so u⁻¹=e*u²/v. No extra puncture is introduced. -/
def overlapInverseU (n : K) : InfinityPuncture n :=
  infinityOpenMap n (globalCubeUnit n : InfinityChart n)*openU n^2*inverseV n
lemma actual_overlap_u_inverse (n : K) : openU n*overlapInverseU n=1 := by
  have hv : openV n=infinityOpenMap n (globalCubeUnit n : InfinityChart n)*openU n^3 := by
    simpa only [map_mul,map_pow] using congrArg (infinityOpenMap n) (actual_global_v_unit_cube n)
  calc
    openU n*overlapInverseU n=
      (infinityOpenMap n (globalCubeUnit n : InfinityChart n)*openU n^3)*inverseV n := by
        unfold overlapInverseU
        ring
    _=openV n*inverseV n := by rw [hv]
    _=1 := actual_open_v_inverse n

def overlapUUnit (n : K) : (InfinityPuncture n)ˣ :=
  Units.mkOfMulEqOne (openU n) (overlapInverseU n) (actual_overlap_u_inverse n)
lemma actual_overlap_inverse_u_isUnit (n : K) : IsUnit (overlapInverseU n) :=
  ((overlapUUnit n)⁻¹).isUnit

def inverseUSection (n : K) : Γ(overlapScheme n,⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (InfinityPuncture n))).inv (overlapInverseU n)
lemma actual_inverse_u_section_isUnit (n : K) : IsUnit (inverseUSection n) :=
  (actual_overlap_inverse_u_isUnit n).map
    (Scheme.ΓSpecIso (CommRingCat.of (InfinityPuncture n))).inv.hom

/-- The inverse-infinity transition is a genuine invertible O-linear
map on the whole common chart. Its direction is u⁻¹, not u. -/
instance inverseUSection_multiply_isIso (n : K) :
    IsIso (ClutchedModule318.multiply (inverseUSection n)) :=
  ClutchedModule318.multiply_isIso _ (actual_inverse_u_section_isUnit n)
lemma actual_inverse_u_section_value (n : K) :
    (Scheme.ΓSpecIso (CommRingCat.of (InfinityPuncture n))).hom (inverseUSection n)=overlapInverseU n :=
  CategoryTheory.Iso.inv_hom_id_apply _ _
end ActualTwoDescentOriginalInverseInfinityTransition318
