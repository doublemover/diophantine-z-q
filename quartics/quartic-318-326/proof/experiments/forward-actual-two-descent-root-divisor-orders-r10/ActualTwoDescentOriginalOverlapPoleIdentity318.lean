module
public import ActualTwoDescentOriginalNativeSquareProduct318
public section
noncomputable section
namespace ActualTwoDescentOriginalOverlapPoleIdentity318
open ActualTwoDescentAffineChartCoordinates318 ActualTwoDescentRootCofactorData318
open ActualTwoDescentOriginalRootIdeals318 ActualTwoDescentInfinityChartRing318
open ActualTwoDescentOriginalPuncturedCharts318 ActualTwoDescentOriginalOverlapQuotientMaps318
open ActualTwoDescentInfinityGlobalFactorUnit318 ActualTwoDescentInfinityGlobalRootUnits318
open ActualTwoDescentOriginalGlobalInfinityPoleUnit318 ActualTwoDescentOriginalInverseInfinityTransition318
variable {K : Type*} [Field K] [CharZero K]

def overlapRoot (n : K) (i : Fin 3) : InfinityPuncture n :=
  affineToInfinity n (rootNumerator n i)

/-- Exact pole identity INSIDE the literal overlap ring,not only after
embedding in a field. Both cancellations use produced actual units. -/
lemma actual_overlap_pole (n : K) (i : Fin 3) :
    overlapRoot n i*openU n^2=infinityOpenMap n (rootPoleUnit n i : InfinityChart n) := by
  let e := Units.map (infinityOpenMap n).toMonoidHom (globalCubeUnit n)
  let d := Units.map (infinityOpenMap n).toMonoidHom (globalRootUnit n i)
  have hv : openV n=(e : InfinityPuncture n)*openU n^3 := by
    simpa only [map_mul,map_pow] using congrArg (infinityOpenMap n) (actual_global_v_unit_cube n)
  have hd : openU n-infinityOpenCoefficient n (root n i)*openV n=openU n*(d : InfinityPuncture n) := by
    have h := congrArg (infinityOpenMap n) (actual_global_root_numerator n i)
    rw [←actual_global_root_unit_value] at h
    simpa only [map_sub,map_mul] using h
  have hf : overlapRoot n i*openV n=openU n-infinityOpenCoefficient n (root n i)*openV n := by
    unfold overlapRoot rootNumerator
    rw [map_sub,actual_affine_to_infinity_x,actual_affine_to_infinity_coefficient]
    linear_combination openU n*(actual_open_v_inverse n)
  have hprod : (overlapRoot n i*openU n^2)*(e : InfinityPuncture n)=(d : InfinityPuncture n) := by
    apply (overlapUUnit n).isUnit.mul_left_cancel
    change openU n*((overlapRoot n i*openU n^2)*(e : InfinityPuncture n))=openU n*(d : InfinityPuncture n)
    calc
      _=overlapRoot n i*((e : InfinityPuncture n)*openU n^3) := by ring
      _=overlapRoot n i*openV n := by rw [hv]
      _=_ := hf.trans hd
  apply e.isUnit.mul_right_cancel
  rw [hprod]
  change (d : InfinityPuncture n)=infinityOpenMap n
    ((globalRootUnit n i : InfinityChart n)*
      (((globalCubeUnit n)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n))*(e : InfinityPuncture n)
  rw [map_mul]
  change (d : InfinityPuncture n)=
    ((d : InfinityPuncture n)*((e⁻¹ : (InfinityPuncture n)ˣ) : InfinityPuncture n))*(e : InfinityPuncture n)
  rw [mul_assoc,Units.inv_mul,mul_one]

def overlapRootUnit (n : K) (i : Fin 3) : (InfinityPuncture n)ˣ :=
  (Units.map (infinityOpenMap n).toMonoidHom (rootPoleUnit n i))*(overlapUUnit n)⁻¹^2
lemma actual_overlap_root_unit (n : K) (i : Fin 3) :
    (overlapRootUnit n i : InfinityPuncture n)=overlapRoot n i := by
  change infinityOpenMap n (rootPoleUnit n i : InfinityChart n)*overlapInverseU n^2=overlapRoot n i
  rw [←actual_overlap_pole]
  calc
    _=overlapRoot n i*(openU n*overlapInverseU n)^2 := by ring
    _=_ := by rw [actual_overlap_u_inverse,one_pow,mul_one]

/-- The EXACT inverse pole coefficient has the square of the original
b/u transition. This fixes both the direction and the scalar. -/
lemma actual_overlap_square_coefficient (n : K) (i : Fin 3) :
    overlapRoot n i*infinityOpenMap n (((rootPoleUnit n i)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n)=
      overlapInverseU n^2 := by
  have h := congrArg (fun z : InfinityPuncture n =>
    z*infinityOpenMap n (((rootPoleUnit n i)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n))
      (actual_overlap_root_unit n i)
  have hp := congrArg (infinityOpenMap n) (Units.mul_inv (rootPoleUnit n i))
  simp only [map_mul,map_one] at hp
  change (infinityOpenMap n (rootPoleUnit n i : InfinityChart n)*overlapInverseU n^2)*
    infinityOpenMap n (((rootPoleUnit n i)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n)=
    overlapRoot n i*infinityOpenMap n (((rootPoleUnit n i)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n) at h
  calc
    _=(infinityOpenMap n (rootPoleUnit n i : InfinityChart n)*overlapInverseU n^2)*
      infinityOpenMap n (((rootPoleUnit n i)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n) := h.symm
    _=overlapInverseU n^2*(infinityOpenMap n (rootPoleUnit n i : InfinityChart n)*
      infinityOpenMap n (((rootPoleUnit n i)⁻¹ : (InfinityChart n)ˣ) : InfinityChart n)) := by ring
    _=_ := by rw [hp,mul_one]
end ActualTwoDescentOriginalOverlapPoleIdentity318
