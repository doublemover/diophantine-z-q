module
public import OriginalReducedFibreSaturation318
import all OriginalReducedFibreSaturation318
public import Mathlib.Tactic
public section

/-! On one original arithmetic affine over Z[1/n], a single integer clears
both the Q-fibre restriction and its localization. Only the finitely many
rational primes that divide that integer need to be inspected. -/
namespace OriginalIntegerAffineExtend318
open OriginalReducedFibreSaturation318
variable {K : Type*} [Field K] [CharZero K] (A : Subring K)

/-- Membership in the actual prime localization as a fraction in K.
For arbitrary x, equality in K encodes both signs and common scaling. -/
def HasStalkValue (q : Ideal A) (x : K) : Prop :=
  ∃ s : A, s ∉ q ∧ ∃ c : A, (s:K)*x=(c:K)

omit [CharZero K] in
theorem from_localization {q : Ideal A} [q.IsPrime] (V : Subring K) (hAV : A ≤ V)
    (loc : letI := (Subring.inclusion hAV).toAlgebra; IsLocalization q.primeCompl V)
    {x : K} (hx : x ∈ V) : HasStalkValue A q x := by
  let : Algebra A V := (Subring.inclusion hAV).toAlgebra
  let : IsLocalization q.primeCompl V := loc
  obtain ⟨⟨c,s⟩,he⟩ := IsLocalization.surj q.primeCompl (⟨x,hx⟩:V)
  refine ⟨s.1,s.2,c,?_⟩
  have e := congrArg V.subtype he
  change x*(s.1 : K)=(c:K) at e
  exact (mul_comm _ _).trans e

private theorem strip_prime (x : K) (p m : ℕ) (hp : p.Prime)
    (hred : IsReduced (A ⧸ Ideal.span ({(p:A)} : Set A)))
    (hlocal : ∀ q : Ideal A,(Ideal.span ({(p:A)} : Set A)).IsMinimalPrime q → HasStalkValue A q x)
    (a : A) (ha : (a:K)=(p:K)*(m:K)*x) : ∃ b : A,(b:K)=(m:K)*x := by
  have hc : Clears (p:A) a 1 := by
    intro q hq
    obtain ⟨s,hs,c,he⟩ := hlocal q hq
    refine ⟨s,hs,(m:A)*c,?_⟩
    apply Subtype.ext
    change (s:K)*(a:K)=((p:A):K)^1*(((m:A):K)*(c:K))
    rw [ha,←he,pow_one]
    push_cast
    ring
  have hn : (p:A)≠0 := Nat.cast_ne_zero.mpr hp.ne_zero
  obtain ⟨b,hb⟩ := divisibility_at_reduced_fibre (isRegular_iff_ne_zero.mpr hn) hred hc
  simp only [pow_one] at hb
  refine ⟨b,?_⟩
  apply mul_left_cancel₀ (show (p:K) ≠ 0 from Nat.cast_ne_zero.mpr hp.ne_zero)
  calc (p:K)*(b:K) = (a:K) := by
         have he := congrArg A.subtype hb.symm
         rw [map_mul,map_natCast] at he; exact he
       _ = _ := by rw [ha]; ring

/-- No family of integer-local rings or patching datum is supplied:
the lift is constructed in A on this entire affine. The ideal (p) can
have multiple components; every minimal prime is explicitly tested. -/
theorem extend_from_single_integer (x : K) (N : ℕ) (hN : N≠0)
    (a : A) (ha : (a:K)=(N:K)*x)
    (fibre : ∀ p : ℕ,p.Prime → p ∣ N → IsReduced (A ⧸ Ideal.span ({(p:A)} : Set A)))
    (stalks : ∀ p : ℕ,p.Prime → p ∣ N → ∀ q : Ideal A,
      (Ideal.span ({(p:A)} : Set A)).IsMinimalPrime q → HasStalkValue A q x) :
    x ∈ A := by
  induction N using Nat.strong_induction_on generalizing a with
  | h n ih =>
    by_cases one : n=1
    · have e : (a:K)=x := by simpa [one] using ha
      exact e ▸ a.property
    obtain ⟨p,hp,m,hm⟩ := Nat.exists_prime_and_dvd one
    have pd : p∣n := ⟨m,hm⟩
    have m0 : m≠0 := by intro h; exact hN (by simp [hm,h])
    have lt : m<n := by rw [hm]; nlinarith [hp.two_le,Nat.one_le_iff_ne_zero.mpr m0]
    have dm : m∣n := ⟨p,by rw [hm,mul_comm]⟩
    obtain ⟨b,hb⟩ := strip_prime A x p m hp (fibre p hp pd) (stalks p hp pd) a
      (by simpa only [hm,Nat.cast_mul] using ha)
    exact ih m lt m0 b hb (fun q hq hd => fibre q hq (hd.trans dm))
      (fun q hq hd => stalks q hq (hd.trans dm))

/-- Multiplicative system identifying the full rational generic fibre
on a Z[1/n]-affine; allowing negative integers in addition changes nothing. -/
def positiveIntegers : Submonoid A where
  carrier a := ∃ n : ℕ,n≠0 ∧ (n:A)=a
  one_mem' := ⟨1,one_ne_zero,Nat.cast_one⟩
  mul_mem' := by
    rintro a b ⟨m,hm,rfl⟩ ⟨n,hn,rfl⟩
    exact ⟨m*n,mul_ne_zero hm hn,Nat.cast_mul m n⟩

omit [CharZero K] in
theorem denominator_of_generic (G : Subring K) (hAG : A ≤ G)
    (generic : letI := (Subring.inclusion hAG).toAlgebra; IsLocalization (positiveIntegers A) G)
    {x : K} (hx : x∈G) : ∃ (N : ℕ), N≠0 ∧ ∃ a : A,(a:K)=(N:K)*x := by
  let : Algebra A G := (Subring.inclusion hAG).toAlgebra
  let : IsLocalization (positiveIntegers A) G := generic
  obtain ⟨⟨a,s⟩,he⟩ := IsLocalization.surj (positiveIntegers A) (⟨x,hx⟩:G)
  obtain ⟨n,hn,hns⟩ := s.property
  refine ⟨n,hn,a,?_⟩
  have ee := congrArg G.subtype he
  change x*((s:A):K)=(a:K) at ee
  rw [←hns] at ee
  have sc : ((n:A):K)=(n:K) := map_natCast A.subtype n
  rw [sc] at ee
  exact ee.symm.trans (mul_comm _ _)

end OriginalIntegerAffineExtend318
