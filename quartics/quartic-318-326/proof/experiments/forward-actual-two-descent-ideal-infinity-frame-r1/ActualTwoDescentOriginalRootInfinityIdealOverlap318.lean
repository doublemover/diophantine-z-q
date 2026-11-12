module
public import ActualTwoDescentOriginalCubicChartCover318
public section
noncomputable section
namespace ActualTwoDescentOriginalRootInfinityIdealOverlap318
open ActualTwoDescentEllipticModel318 ActualTwoDescentAffineChartCoordinates318
open ActualTwoDescentInfinityChartRing318 ActualTwoDescentInfinityLocalParameter318
open ActualTwoDescentOriginalRootIdeals318 ActualTwoDescentOriginalPuncturedCharts318
open ActualTwoDescentOriginalOverlapQuotientMaps318
open WeierstrassCurve.Affine.CoordinateRing
variable {K : Type*} [Field K] [CharZero K]

lemma actual_affine_y_mem_root_ideal (n : K) (i : Fin 3) : affineY n ∈ rootIdeal n i := by
  have h : YClass (curve n).toAffine 0 ∈ rootIdeal n i :=
    Ideal.subset_span (by simp [rootIdeal,XYIdeal])
  simpa only [YClass,Polynomial.C_0,sub_zero] using h

/-- The ACTUAL affine root ideal becomes the unit ideal on the literal
common chart. Its trivialization uses the original y generator and its
actual inverse, not a dimension-one argument. -/
theorem actual_root_ideal_overlap (n : K) (i : Fin 3) :
    Ideal.map (affineToInfinity n) (rootIdeal n i)=⊤ := by
  apply Ideal.eq_top_iff_one.mpr
  have hy := Ideal.mem_map_of_mem (affineToInfinity n) (actual_affine_y_mem_root_ideal n i)
  rw [actual_affine_to_infinity_y] at hy
  have h := (Ideal.map (affineToInfinity n) (rootIdeal n i)).mul_mem_left (openV n) hy
  simpa only [actual_open_v_inverse] using h

/-- The actual infinity ideal is also trivial on the SAME overlap,
because the literal v belongs to it and is inverted there. -/
theorem actual_origin_ideal_overlap (n : K) :
    Ideal.map (infinityOpenMap n) (originIdeal n)=⊤ := by
  apply Ideal.eq_top_iff_one.mpr
  have hv : chartV n ∈ originIdeal n := actual_origin_v n
  have hh := Ideal.mem_map_of_mem (infinityOpenMap n) hv
  have h := (Ideal.map (infinityOpenMap n) (originIdeal n)).mul_mem_left (inverseV n) hh
  change inverseV n*openV n ∈ _ at h
  simpa only [mul_comm,actual_open_v_inverse] using h

/-- Both original ideal restrictions agree as literal ideals of the
same overlap ring. Module-sheaf descent and the Ta−O tensor-square
identification remain separate work, rather than built into this equality. -/
theorem actual_root_origin_overlap_match (n : K) (i : Fin 3) :
    Ideal.map (affineToInfinity n) (rootIdeal n i)=
      Ideal.map (infinityOpenMap n) (originIdeal n) := by
  rw [actual_root_ideal_overlap,actual_origin_ideal_overlap]
end ActualTwoDescentOriginalRootInfinityIdealOverlap318
