module
public import SelectedFixedEntrySupport318
public section
namespace NatDivisorDropCertificate318
/-- If a prime factor can NOT be dropped from an upper multiple, that
prime must divide the actual divisor. Primality is essential. -/
theorem prime_divides (n N q : ℕ) (hq : q.Prime) (hN : q∣N)
    (hn : n∣N) (hdrop : ¬n∣N/q) : q∣n := by
  by_contra hqn
  have hcop : Nat.Coprime n q := (hq.coprime_iff_not_dvd.mpr hqn).symm
  have hm : n∣q*(N/q) := by simpa only [Nat.mul_div_cancel' hN] using hn
  exact hdrop (hcop.dvd_of_dvd_mul_left hm)
lemma quotient_positive (N q : ℕ) (hN : 0<N) (hq : q.Prime) (hd : q∣N) : 0<N/q := by
  have he:=Nat.mul_div_cancel' hd
  by_contra hz
  have hzero : N/q=0 := by omega
  rw [hzero,mul_zero] at he
  omega
end NatDivisorDropCertificate318
