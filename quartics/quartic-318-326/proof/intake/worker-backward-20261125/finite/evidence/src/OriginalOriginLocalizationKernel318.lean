module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Ideal

@[expose] public section
noncomputable section

namespace OriginalOriginLocalizationKernel318

variable {B L T : Type*} [CommRing B] [CommRing L] [CommRing T]
variable (P : Ideal B) [P.IsPrime] [Algebra B L] [IsLocalization.AtPrime L P]
variable (v : B→+*T) (den : ∀ s : P.primeCompl, IsUnit (v s))

/-- Localize the specified evaluation at its original closed point;
the target does not get localized or replaced. -/
def onLocalRing : L→+*T := IsLocalization.lift den

theorem onLocalRing_read (x : B) :
    onLocalRing P v den (algebraMap B L x)=v x :=
  IsLocalization.lift_eq den x

theorem onLocalRing_unique (q : L→+*T) (pin : q.comp (algebraMap B L)=v) :
    q=onLocalRing P v den := by
  apply IsLocalization.ringHom_ext P.primeCompl
  apply RingHom.ext
  intro x
  exact (RingHom.congr_fun pin x).trans (onLocalRing_read P v den x).symm

/-- The actual germ of the evaluation has exactly the extended
kernel. A denominator already invertible in the target is not an
additional component or a saturated replacement kernel. -/
theorem onLocalRing_ker :
    RingHom.ker (onLocalRing P v den : L→+*T)=(RingHom.ker v).map (algebraMap B L) := by
  apply le_antisymm
  · intro z hz
    obtain ⟨a,s,rfl⟩ := IsLocalization.exists_mk'_eq P.primeCompl z
    have e : (onLocalRing P v den : L→+*T) (IsLocalization.mk' L a s)=0 :=
      RingHom.mem_ker.1 hz
    have e' : v a=0 := by
      have eq := (IsLocalization.lift_mk'_spec (S:=L) den a 0 s).1 e
      rwa [mul_zero] at eq
    apply (IsLocalization.mk'_mem_iff (y:=s)).2
    exact Ideal.mem_map_of_mem (algebraMap B L) (RingHom.mem_ker.2 e')
  · apply (Ideal.map_le_iff_le_comap).2
    intro a ha
    apply RingHom.mem_ker.2
    rw [onLocalRing_read]
    exact RingHom.mem_ker.1 ha

variable [IsLocalRing L]

/-- In the actual origin local ring this is a power of its own
maximal ideal. In particular exponent two means the full actual
first-order germ, not just its residue or its discard of nilpotents. -/
theorem onLocalRing_ker_power (k : ℕ) (h : RingHom.ker v=P^k) :
    RingHom.ker (onLocalRing P v den : L→+*T)=(IsLocalRing.maximalIdeal L)^k := by
  rw [onLocalRing_ker,h,Ideal.map_pow,IsLocalization.AtPrime.map_eq_maximalIdeal P L]

end OriginalOriginLocalizationKernel318
