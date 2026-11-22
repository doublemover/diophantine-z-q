module
public import ActualGaussianWeberActualLocalizedFrob318
public import ActualGaussianWeberPlaceEquivariance318
public section
noncomputable section

namespace ActualGaussianWeberActualPointFrob318

open NumberField IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberChosenPlaceLift318
open ActualGaussianWeberIntegerModel318 ActualGaussianWeberCanonicalRingFrob318
open ActualGaussianWeberActualLocalizedFrob318
open ActualGaussianWeberHenselianPointMap318 ActualGaussianWeberPlaceEquivariance318

variable (L : Type*) [Field L] [NumberField L] [Algebra Base L]
variable [FiniteDimensional Base L] [IsGalois Base L]
variable {p : ℕ} [Fact p.Prime]
variable (w : HeightOneSpectrum (𝓞 L)) (j : ZMod p) (hj : j^2 = -1)
variable (hUnder : SignedAt L w j hj)

include hUnder in
@[expose] def residueArithmeticFrob : ResidueField (AtPlace L w) →+* ResidueField (AtPlace L w) := by
  letI := integralAlgebra (algebraMap Base L)
  letI : CharP (ResidueField (AtPlace L w)) p := actual_residue_char (L := L) w j hj hUnder
  exact frobenius (ResidueField (AtPlace L w)) p

theorem residue_arithmetic_frob_apply (r : ResidueField (AtPlace L w)) :
    residueArithmeticFrob L w j hj hUnder r=r^p := by
  unfold residueArithmeticFrob
  rfl

include hUnder in
theorem fixed_actual_place :
    (AtPlace L w).comap (arithAt L w).toRingEquiv.toRingHom=AtPlace L w := by
  let V := AtPlace L w
  let σ := (arithAt L w).toRingEquiv
  let e := localFrob L w j hj hUnder
  apply (same_place_iff V σ).mpr
  intro x
  constructor
  · intro hx
    let z : V := ⟨σ x,hx⟩
    let a := e.symm z
    have h := localFrob_field L w j hj hUnder a
    change V.subtype (e (e.symm z))=σ (V.subtype a) at h
    rw [RingEquiv.apply_symm_apply] at h
    have ha : V.subtype a=x := σ.injective h.symm
    have hV : V.subtype a∈V := a.property
    simpa only [ha] using hV
  · intro hx
    let z : V := ⟨x,hx⟩
    have hz : V.subtype (e z)∈V := (e z).property
    have h := localFrob_field L w j hj hUnder z
    change V.subtype (e z)=σ x at h
    simpa only [h] using hz

theorem restricted_equals_local_frob (x : AtPlace L w) :
    restrict (AtPlace L w) (arithAt L w).toRingEquiv
      (fixed_actual_place L w j hj hUnder) x=localFrob L w j hj hUnder x := by
  apply Subtype.ext
  exact (localFrob_field L w j hj hUnder x).symm

theorem residue_point_map_exact :
    (residueSigma (AtPlace L w) (arithAt L w).toRingEquiv
      (fixed_actual_place L w j hj hUnder)).toRingHom =
      residueArithmeticFrob L w j hj hUnder := by
  apply RingHom.ext
  intro r
  obtain ⟨x,rfl⟩ := residue_surjective r
  change (residueSigma (AtPlace L w) (arithAt L w).toRingEquiv
      (fixed_actual_place L w j hj hUnder)) (residue (AtPlace L w) x) =
    residueArithmeticFrob L w j hj hUnder (residue (AtPlace L w) x)
  calc
    _ = residue (AtPlace L w)
        (restrict (AtPlace L w) (arithAt L w).toRingEquiv
          (fixed_actual_place L w j hj hUnder) x) :=
      residueSigma_residue (AtPlace L w) (arithAt L w).toRingEquiv
        (fixed_actual_place L w j hj hUnder) x
    _ = residue (AtPlace L w) (localFrob L w j hj hUnder x) :=
      congrArg (residue (AtPlace L w)) (restricted_equals_local_frob L w j hj hUnder x)
    _ = (residue (AtPlace L w) x)^p := localFrob_residue_pow L w j hj hUnder x
    _ = _ := (residue_arithmetic_frob_apply L w j hj hUnder (residue (AtPlace L w) x)).symm

/-- On the actual stock curve and the actual signed Gaussian prime
of the original number field, arithmetic Frobenius specializes to
the coordinate p-power on **every** point, including infinity and
all points reducing to infinity. No claim about scalar [π] yet. -/
theorem actual_frob_point_specializes (h2 : (2:ZMod p) ≠ 0) (P : WP L) :
    let hR : (2:ResidueField (AtPlace L w)) ≠ 0 := by
      letI := integralAlgebra (algebraMap Base L)
      exact residue_two_ne w j hj hUnder h2
    specialize (AtPlace L w) hR (onCurvePoint (arithAt L w).toRingEquiv.toRingHom
        (by norm_num : (2:L) ≠ 0) P) =
      onCurvePoint (residueArithmeticFrob L w j hj hUnder) hR (specialize (AtPlace L w) hR P) := by
  letI := integralAlgebra (algebraMap Base L)
  let hR : (2 : ResidueField (AtPlace L w)) ≠ 0 := residue_two_ne (L := L) w j hj hUnder h2
  change specialize (AtPlace L w) hR _ = _
  rw [specialize_sigma (AtPlace L w) (by norm_num : (2:L) ≠ 0) hR
    (arithAt L w).toRingEquiv (fixed_actual_place L w j hj hUnder) P,
    residue_point_map_exact L w j hj hUnder]

end ActualGaussianWeberActualPointFrob318
