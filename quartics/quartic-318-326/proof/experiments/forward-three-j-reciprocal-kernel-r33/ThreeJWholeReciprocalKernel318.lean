module
public import AffineIdealLocalization318
public section
noncomputable section
namespace ThreeJWholeReciprocalKernel318
open AlgebraicGeometry CategoryTheory Polynomial
open ProjectiveLineOverlap318 ThreeJGlobalRamificationScheme318
open ThreeJReciprocalKernelSupport318 ThreeJGlobalDifferentialJoin318
open ThreeJRamificationIdealCharts318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Reciprocal coordinate substitution on the actual Laurent ring. -/
@[expose] def inversion : A →ₐ[ℚ] A :=
  IsLocalization.Away.liftAlgHom (f:=Polynomial.aeval (R:=ℚ) s) (X:ℚ[X])
    (by simpa only [Polynomial.aeval_X] using (IsUnit.of_mul_eq_one_right _ ts))

theorem inversion_t : inversion t=s := by
  change inversion (algebraMap ℚ[X] A X)=s
  rw [inversion,IsLocalization.Away.liftAlgHom_apply,IsLocalization.Away.lift_eq]
  exact Polynomial.aeval_X _

theorem inversion_s : inversion s=t := by
  have h := congrArg inversion ts
  rw [map_mul,map_one,inversion_t] at h
  apply (IsUnit.of_mul_eq_one_right _ ts).mul_left_cancel.mp
  calc
    s * inversion s = 1 := h
    _ = s * t := by rw [mul_comm s t,ts]

theorem inversion_reciprocal :
    inversion.toRingHom.comp (Polynomial.aeval (R:=ℚ) s).toRingHom=algebraMap ℚ[X] A := by
  apply Polynomial.ringHom_ext
  · intro q
    change inversion ((Polynomial.aeval (R:=ℚ) s) (C q))=algebraMap ℚ[X] A (C q)
    rw [Polynomial.aeval_C,AlgHom.commutes]
    exact IsScalarTower.algebraMap_apply ℚ ℚ[X] A q
  · change inversion ((Polynomial.aeval (R:=ℚ) s) X)=t
    rw [Polynomial.aeval_X,inversion_s]

/-- Restriction of the SAME global ideal along the two original projective
routes gives equality on the full Laurent intersection in affine coordinates. -/
theorem actual_overlap :
    reciprocalCoordinateIdeal.map (Polynomial.aeval (R:=ℚ) s).toRingHom=
      finiteCoordinateIdeal.map (algebraMap ℚ[X] A) := by
  have h := congrArg (fun f => ThreeJGlobalRamificationScheme318.ideal.comap f)
    ProjectiveLineOverlap318.maps_agree
  rw [Scheme.IdealSheafData.comap_comp,Scheme.IdealSheafData.comap_comp] at h
  have hc := congrArg AffineIdealCoordinates318.coordinates h
  change AffineIdealCoordinates318.coordinates
      ((ThreeJGlobalRamificationScheme318.ideal.comap (JLineAtlas318.chart ℚ 1)).comap
        (Spec.map (CommRingCat.ofHom (algebraMap ℚ[X] A)))) =
    AffineIdealCoordinates318.coordinates
      ((ThreeJGlobalRamificationScheme318.ideal.comap (JLineAtlas318.chart ℚ 0)).comap
        (Spec.map (CommRingCat.ofHom (Polynomial.aeval (R:=ℚ) s).toRingHom))) at hc
  rw [AffineIdealLocalization318.coordinates_comap,AffineIdealLocalization318.coordinates_comap] at hc
  exact hc.symm

/-- Whole reciprocal-chart ideal equality, including its origin and every
nilpotent component. Exact localization recovery is justified on BOTH sides
by actual quotient units, so no support-only extension is used. -/
theorem whole_reciprocal_equation : reciprocalCoordinateIdeal=Ideal.span {infinityEquation} := by
  apply ThreeJReciprocalKernelCertificate318.recover_reciprocal_ideal _ actual_coordinate_unit
  have h := actual_overlap.trans reciprocal_overlap_join
  have hi := congrArg (Ideal.map inversion.toRingHom) h
  rw [Ideal.map_map,Ideal.map_map,inversion_reciprocal] at hi
  exact hi

/-- The actual global kernel on the entire reciprocal source cusp chart,
under its literal 1/j target action, is the full relative differential
annihilator after extension to the specified numerator localization. -/
theorem infinity_cusp_join (a : ThreeJCuspDifferentialCharts318.InfinityRing) :
    letI := LocalizedRationalDifferentials318.targetAlgebra
      ThreeProjectiveJCertificates318.reciprocalDenominator
      ThreeProjectiveJCertificates318.reciprocalNumerator ThreeJCuspDifferentialCharts318.infinityInverse
    (∀ w : KaehlerDifferential ℚ[X] ThreeJCuspDifferentialCharts318.InfinityRing, a • w=0) ↔
      a ∈ Ideal.map
        (LocalizedRationalDifferentials318.value ThreeProjectiveJCertificates318.reciprocalNumerator).toRingHom
        reciprocalCoordinateIdeal := by
  letI := LocalizedRationalDifferentials318.targetAlgebra
    ThreeProjectiveJCertificates318.reciprocalDenominator
    ThreeProjectiveJCertificates318.reciprocalNumerator ThreeJCuspDifferentialCharts318.infinityInverse
  rw [whole_reciprocal_equation]
  exact ThreeJLocalAnnihilators318.infinity_annihilator a
end ThreeJWholeReciprocalKernel318
