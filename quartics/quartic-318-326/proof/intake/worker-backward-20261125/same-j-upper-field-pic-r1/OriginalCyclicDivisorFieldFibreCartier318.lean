module
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

@[expose] public section
noncomputable section

namespace OriginalCyclicDivisorFieldFibreCartier318

universe u
variable {A E : Type u} [CommRing A] [CommRing E]
variable (g : A →+* E) (x : A) (hx : g x=0)

abbrev J := Ideal.span ({x} : Set A)
abbrev q := Ideal.Quotient.mk (J x)

def fibreRead : (A ⧸ J x) →+* E := by
  have hspan : J x ≤ RingHom.ker g :=
    (Ideal.span_singleton_le_iff_mem (RingHom.ker g)).mpr (RingHom.mem_ker.mpr hx)
  exact Ideal.Quotient.lift (J x) g (fun a ha=>RingHom.mem_ker.mp (hspan ha))

variable (δ : A ⧸ J x)

def retainedDenominator : A :=
  Classical.choose (Ideal.Quotient.mk_surjective (I:=J x) (1-δ))

theorem quotient_denominator : q x (retainedDenominator x δ)=1-δ :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (I:=J x) (1-δ))

variable (he : RingHom.ker (fibreRead g x hx)=Ideal.span {δ})

include he in
theorem retain_read : g (retainedDenominator x δ)=1 := by
  have hzero : fibreRead g x hx δ=0 := by
    change δ∈RingHom.ker (fibreRead g x hx)
    rw [he]
    exact Ideal.subset_span (Set.mem_singleton _)
  change fibreRead g x hx (q x (retainedDenominator x δ))=1
  rw [quotient_denominator,map_sub,map_one,hzero,sub_zero]

abbrev L := Localization.Away (retainedDenominator x δ)
abbrev into := algebraMap A (L x δ)

def locRead : L x δ →+* E :=
  IsLocalization.Away.lift (retainedDenominator x δ)
    (g:=g) (by rw [retain_read g x hx δ he]; exact isUnit_one)

theorem locRead_input (a : A) :
    locRead g x hx δ he (into x δ a)=g a :=
  IsLocalization.Away.lift_eq _ _ _

variable (idempotent : δ*δ=δ)

include he idempotent in
/-- Multiply by the actual denominator of the retained clopen to
kill precisely the discarded fibre-factor ideal. -/
theorem denominator_kills (a : A) (ha : g a=0) :
    retainedDenominator x δ * a ∈ J x := by
  have hm : q x a ∈ Ideal.span {δ} := by
    rw [←he]
    exact ha
  obtain ⟨b,hb⟩ := Ideal.mem_span_singleton'.mp hm
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q x (retainedDenominator x δ*a)=0
  rw [map_mul,quotient_denominator,←hb]
  calc
    (1-δ)*(b*δ) = b*((1-δ)*δ) := by ac_rfl
    _ = 0 := by rw [sub_mul,one_mul,idempotent,sub_self,mul_zero]

include idempotent in
/-- In the actual chart selected by g(t)=1, the full kernel of the
retained read is the principal original fibre equation. -/
theorem localized_kernel : RingHom.ker (locRead g x hx δ he) =
    Ideal.span {into x δ x} := by
  have base : (J x).map (into x δ)=Ideal.span {into x δ x} := by
    rw [Ideal.map_span,Set.image_singleton]
  apply le_antisymm
  · rw [←base]
    intro z hz
    obtain ⟨n,a,ha⟩ :=
      IsLocalization.Away.surj (retainedDenominator x δ) z
    have zero : locRead g x hx δ he z=0 := hz
    have ea : g a=0 := by
      calc
        g a = locRead g x hx δ he (into x δ a) := (locRead_input g x hx δ he a).symm
        _ = _ := by rw [←ha,map_mul,zero,zero_mul]
    have m := Ideal.mem_map_of_mem (into x δ)
      (denominator_kills g x hx δ he idempotent a ea)
    rw [map_mul] at m
    have u : IsUnit (into x δ (retainedDenominator x δ)) :=
      IsLocalization.Away.algebraMap_isUnit _
    have ma := (Ideal.unit_mul_mem_iff_mem ((J x).map (into x δ)) u).mp m
    have zv : into x δ (retainedDenominator x δ)^n * z ∈
        (J x).map (into x δ) := by
      rw [mul_comm,ha]
      exact ma
    exact (Ideal.unit_mul_mem_iff_mem _ (u.pow n)).mp zv
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact (locRead_input g x hx δ he x).trans hx

theorem loc_surj (surj : Function.Surjective g) :
    Function.Surjective (locRead g x hx δ he) := by
  intro z
  obtain ⟨a,rfl⟩ := surj z
  exact ⟨into x δ a,locRead_input g x hx δ he a⟩

include idempotent in
/-- The quotient is the named retained field factor, reading every
coefficient via the same original map g, not a new point over x=0. -/
def retainedQuotient (surj : Function.Surjective g) :
    (L x δ ⧸ Ideal.span {into x δ x}) ≃+* E := by
  rw [←localized_kernel g x hx δ he idempotent]
  exact RingHom.quotientKerEquivOfSurjective (loc_surj g x hx δ he surj)

end OriginalCyclicDivisorFieldFibreCartier318

#print axioms OriginalCyclicDivisorFieldFibreCartier318.localized_kernel
#print axioms OriginalCyclicDivisorFieldFibreCartier318.retainedQuotient
