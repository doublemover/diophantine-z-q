module
public import OriginalAllPrimeAffineSections318
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public section
noncomputable section

namespace OriginalCanonicalVerticalStalk318
open Ring OriginalAllPrimeAffineSections318 OriginalIntegerAffineExtend318
open SelectedActualSameAFiniteDlogRows318 SelectedSameADyadicVerticalD2_318
open scoped nonZeroDivisors
variable {K : Type*} [Field K] [CharZero K]
variable (A : Subring K) [IsFractionRing A K] [IsNoetherianRing A] [IsIntegrallyClosed A]

omit [CharZero K] [IsNoetherianRing A] [IsIntegrallyClosed A] in
/-- Canonical prime localization, represented by its image in Frac(A). -/
theorem embedded_prime (q : Ideal A) [q.IsPrime] :
    ∃ (V : Subring K) (incl : A≤V),
      letI := (Subring.inclusion incl).toAlgebra
      IsLocalization q.primeCompl V ∧ IsFractionRing V K := by
  let S := Localization.AtPrime q
  have units (s : q.primeCompl) : IsUnit ((Algebra.ofId A K) (s:A)) := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    apply s.property
    have e : (s:A)=0 := Subtype.ext h
    rw [e]; exact q.zero_mem
  let f : S →ₐ[A] K := IsLocalization.liftAlgHom (M:=q.primeCompl) units
  have fi : Function.Injective f := by
    apply (IsLocalization.injective_iff_map_algebraMap_eq q.primeCompl f.toRingHom).mpr
    intro x y
    constructor
    · exact fun h => congrArg f h
    · intro h
      change f (algebraMap A S x)=f (algebraMap A S y) at h
      rw [f.commutes,f.commutes] at h
      exact congrArg (algebraMap A S) ((IsFractionRing.injective A K) h)
  let V : Subring K := f.toRingHom.range
  have incl : A≤V := fun x hx => ⟨algebraMap A S (⟨x,hx⟩:A),f.commutes _⟩
  let : Algebra A V := (Subring.inclusion incl).toAlgebra
  let : IsScalarTower A V K := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let ff : S →ₐ[A] V := {f.toRingHom.rangeRestrict with commutes' := fun a => Subtype.ext (f.commutes a)}
  have fbij : Function.Bijective ff :=
    ⟨fun x y e => fi (congrArg V.subtype e), f.toRingHom.rangeRestrict_surjective⟩
  let : IsLocalization q.primeCompl V :=
    IsLocalization.isLocalization_of_algEquiv q.primeCompl (AlgEquiv.ofBijective ff fbij)
  let : IsFractionRing V K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.primeCompl V K
  exact ⟨V,incl,inferInstance,inferInstance⟩

/-- The needed actual subring is the image of the CANONICAL prime
localization in the original function field, not a DVR picked with a
matching residue characteristic. The reducedness test is localized. -/
theorem canonical_stalk (p : ℕ) (hp : p.Prime)
    (hred : IsReduced (A ⧸ Ideal.span ({(p:A)} : Set A)))
    (q : Ideal A) (hq : (Ideal.span ({(p:A)} : Set A)).IsMinimalPrime q) :
    letI : q.IsPrime := hq.isPrime; Nonempty (OriginalStalk A q p) := by
  let : q.IsPrime := hq.isPrime
  let I := Ideal.span ({(p:A)} : Set A)
  have pnz : (p:A)≠0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hheight : q.height=1 := le_antisymm
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes I q hq)
    ((Ideal.one_le_height_span_singleton_of_mem_nonZeroDivisors
      (mem_nonZeroDivisors_iff_ne_zero.mpr pnz)).trans (Ideal.height_mono hq.le))
  obtain ⟨V,incl,loc,frac⟩ := embedded_prime A q
  let : Algebra A V := (Subring.inclusion incl).toAlgebra
  let : IsLocalization q.primeCompl V := loc
  let : IsFractionRing V K := frac
  let : IsIntegrallyClosed V := isIntegrallyClosed_of_isLocalization V q.primeCompl q.primeCompl_le_nonZeroDivisors
  let : IsNoetherianRing V := IsLocalization.isNoetherianRing q.primeCompl V inferInstance
  let : IsLocalRing V := IsLocalization.AtPrime.isLocalRing V q
  have dim1 : ringKrullDim V=1 := by rw [IsLocalization.AtPrime.ringKrullDim_eq_height q V,hheight]; rfl
  let : Ring.KrullDimLE 1 V := Ring.krullDimLE_iff.mpr (le_of_eq dim1)
  let : Ring.DimensionLEOne V := ⟨fun hq' hqp => hqp.isMaximal_of_ne_bot hq'⟩
  let : IsDedekindRing V :=
    { (inferInstance:IsNoetherianRing V), (inferInstance:Ring.DimensionLEOne V),
      (inferInstance:IsIntegralClosure V V (FractionRing V)) with }
  have nfield : ¬IsField V := IsLocalization.AtPrime.not_isField A (Ideal.ne_bot_of_height_eq_one hheight) V
  have dvr : IsDiscreteValuationRing V :=
    ((IsDiscreteValuationRing.TFAE V nfield).out 1 3).mpr (inferInstance:IsDedekindDomain V)
  have im : I.map (algebraMap A V)=Ideal.span ({(p:V)} : Set V) := by
    rw [Ideal.map_span,Set.image_singleton,map_natCast]
  have hr : I.IsRadical := (Ideal.isRadical_iff_quotient_reduced I).mpr hred
  have red : IsReduced (V ⧸ Ideal.span ({(p:V)} : Set V)) := by
    rw [←im]
    apply (Ideal.isRadical_iff_quotient_reduced _).mp
    apply Ideal.radical_eq_iff.mp
    rw [←IsLocalization.map_radical (M:=q.primeCompl) (S:=V),hr.radical]
  have nunit : ¬IsUnit (p:V) := by
    intro h
    have he : IsUnit (algebraMap A V (p:A)) := by simpa only [map_natCast] using h
    exact (IsLocalization.AtPrime.isUnit_to_map_iff V q (p:A)).mp he (hq.le (Ideal.mem_span_singleton_self _))
  exact ⟨⟨V,incl,inferInstance,dvr,inferInstance,nunit,red⟩⟩

/-- No local DVR, prime tests, frame/field agreements, exposed valuation
inequalities, characteristic-specific arguments or named elliptic half
maps remain as caller fields. Generic and special fibres are those of
ONE noetherian normal original affine with reduced arithmetic fibres. -/
theorem produce_pair [Algebra ℚ K] (G : Subring K) (hAG : A≤G)
    (generic : letI := (Subring.inclusion hAG).toAlgebra; IsLocalization (positiveIntegers A) G)
    (fibre : ∀ p : ℕ,p.Prime → IsReduced (A ⧸ Ideal.span ({(p:A)} : Set A)))
    (frame : KaehlerDifferential ℤ A →ₗ[A] A) (t : K)
    (roots : Fin 4 → K) (twists : Fin 4 → ℚˣ)
    (hn : ∀ i,contact t i≠0)
    (he : ∀ i,roots i^2=algebraMap ℚ K (twists i:ℚ)*contact t i)
    (hgeneric :
      (25725/4:K)*32*qcoeff t (fractionDerivative A frame t)∈G ∧
      (25725/4:K)*t*qcoeff t (fractionDerivative A frame t)∈G) :
      (25725/4:K)*32*qcoeff t (fractionDerivative A frame t)∈A ∧
      (25725/4:K)*t*qcoeff t (fractionDerivative A frame t)∈A :=
  original_affine_sections A G hAG generic fibre
    (fun p hp q hq => canonical_stalk A p hp (fibre p hp) q hq) frame t roots twists hn he hgeneric

end OriginalCanonicalVerticalStalk318
