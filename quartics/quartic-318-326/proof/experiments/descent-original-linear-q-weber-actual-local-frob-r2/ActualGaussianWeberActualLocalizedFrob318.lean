module
public import ActualGaussianWeberCanonicalRingFrob318
public import Mathlib.Algebra.CharP.Frobenius
public section
noncomputable section

namespace ActualGaussianWeberActualLocalizedFrob318

open NumberField IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ActualGaussianWeberSelectedGaussianPrime318 ActualGaussianWeberChosenPlaceLift318
open ActualGaussianWeberIntegerModel318 ActualGaussianWeberCanonicalRingFrob318

variable (L : Type*) [Field L] [NumberField L] [Algebra Base L]
variable [FiniteDimensional Base L] [IsGalois Base L]
variable {p : ℕ} [Fact p.Prime]
variable (w : HeightOneSpectrum (𝓞 L)) (j : ZMod p) (hj : j^2 = -1)

abbrev AtPlace := OverPlace (L:=L) w
abbrev SignedAt :=
  letI := integralAlgebra (algebraMap Base L)
  w.asIdeal.under GaussianInt=selectedIdeal j hj

@[expose] def onIntegers : (𝓞 L)≃+*(𝓞 L) :=
  MulSemiringAction.toRingEquiv (L≃ₐ[Base]L) (𝓞 L) (arithAt L w)

theorem quotient_integer_power (hUnder : SignedAt L w j hj) (x : 𝓞 L) :
    Ideal.Quotient.mk w.asIdeal (onIntegers L w x) =
      (Ideal.Quotient.mk w.asIdeal x)^p := by
  have h := (Ideal.Quotient.eq_zero_iff_mem).mpr (chosen_signed_exponent L w j hj hUnder x)
  rw [map_sub,map_pow,sub_eq_zero] at h
  exact h

theorem onIntegers_mem_iff (hUnder : SignedAt L w j hj) (x : 𝓞 L) :
    onIntegers L w x ∈ w.asIdeal ↔ x ∈ w.asIdeal := by
  constructor
  · intro hx
    have h : (Ideal.Quotient.mk w.asIdeal x)^p=0 :=
      (quotient_integer_power L w j hj hUnder x).symm.trans
        (Ideal.Quotient.eq_zero_iff_mem.mpr hx)
    exact Ideal.Quotient.eq_zero_iff_mem.mp (pow_eq_zero h)
  · intro hx
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [quotient_integer_power L w j hj hUnder,Ideal.Quotient.eq_zero_iff_mem.mpr hx,
      zero_pow (Fact.out : p.Prime).ne_zero]

private theorem primeCompl_maps (hUnder : SignedAt L w j hj) :
    w.asIdeal.primeCompl.map (onIntegers L w).toMonoidHom = w.asIdeal.primeCompl := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact Ideal.mem_primeCompl_iff.mpr
      (fun hy => (Ideal.mem_primeCompl_iff.mp hx) ((onIntegers_mem_iff L w j hj hUnder x).1 hy))
  · intro hy
    let e := onIntegers L w
    refine ⟨e.symm y, Ideal.mem_primeCompl_iff.mpr ?_,e.apply_symm_apply y⟩
    intro hx
    have he : e (e.symm y)∈w.asIdeal := (onIntegers_mem_iff L w j hj hUnder _).2 hx
    exact (Ideal.mem_primeCompl_iff.mp hy) (e.apply_symm_apply y ▸ he)

/-- Literal localization of the canonical integral automorphism
at the same height-one prime. Its ambient field map is not chosen
a second time. -/
@[expose] def localFrob (hUnder : SignedAt L w j hj) :
    AtPlace L w ≃+* AtPlace L w :=
  IsLocalization.ringEquivOfRingEquiv (AtPlace L w) (AtPlace L w) (onIntegers L w)
    (by exact primeCompl_maps L w j hj hUnder)

theorem localFrob_on_integers (hUnder : SignedAt L w j hj) (x : 𝓞 L) :
    localFrob L w j hj hUnder (algebraMap (𝓞 L) (AtPlace L w) x)=
      algebraMap (𝓞 L) (AtPlace L w) (onIntegers L w x) := by
  exact IsLocalization.ringEquivOfRingEquiv_eq (AtPlace L w) (AtPlace L w)
    (primeCompl_maps L w j hj hUnder) x

/-- The stock fraction-field action agrees on every element of the
literal valuation ring, by the universal property of localizing. -/
theorem localFrob_field (hUnder : SignedAt L w j hj) (x : AtPlace L w) :
    (AtPlace L w).subtype (localFrob L w j hj hUnder x) =
      arithAt L w ((AtPlace L w).subtype x) := by
  let V := AtPlace L w
  let σ := (arithAt L w).toRingEquiv.toRingHom
  let a := (localFrob L w j hj hUnder).toRingHom
  have h : V.subtype.comp a=σ.comp V.subtype := by
    apply IsLocalization.ringHom_ext w.asIdeal.primeCompl
    apply RingHom.ext
    intro y
    change V.subtype (localFrob L w j hj hUnder (algebraMap (𝓞 L) V y)) =
      arithAt L w (V.subtype (algebraMap (𝓞 L) V y))
    rw [localFrob_on_integers]
    change algebraMap V L (algebraMap (𝓞 L) V (onIntegers L w y))=
      arithAt L w (algebraMap V L (algebraMap (𝓞 L) V y))
    simp only [←IsScalarTower.algebraMap_apply (𝓞 L) V L]
    exact chosen_actual_field_action L w y
  exact DFunLike.congr_fun h x

/-- The canonical chosen arithmetic automorphism induces the actual
p-th power on the **whole** residue of the same chosen place. It is
proved by comparing two ring maps from the localization on integral
generators, not by assuming a residue map, a copy of Frob, or a
valuation-stability axiom. -/
theorem localFrob_residue_pow (hUnder : SignedAt L w j hj) (x : AtPlace L w) :
    residue (AtPlace L w) (localFrob L w j hj hUnder x) = (residue (AtPlace L w) x)^p := by
  let V := AtPlace L w
  letI := integralAlgebra (algebraMap Base L)
  letI := actual_residue_char w j hj hUnder
  let h := IsLocalization.AtPrime.equivQuotMaximalIdeal w.asIdeal V
  let f := (residue V).comp (localFrob L w j hj hUnder).toRingHom
  let g := (frobenius (ResidueField V) p).comp (residue V)
  have he : f=g := by
    apply IsLocalization.ringHom_ext w.asIdeal.primeCompl
    apply RingHom.ext
    intro y
    change residue V (localFrob L w j hj hUnder (algebraMap (𝓞 L) V y)) =
      (residue V (algebraMap (𝓞 L) V y))^p
    rw [localFrob_on_integers]
    have e := congrArg h (quotient_integer_power L w j hj hUnder y)
    simpa only [map_pow,h,IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk,residue_def] using e
  exact DFunLike.congr_fun he x

end ActualGaussianWeberActualLocalizedFrob318
