module
public import DegenerateDetector
public section
namespace DegenerateContacts

@[expose] def phi (t : ℚ) : ℚ := 2+1/t
@[expose] def contactProduct (r : ℚ) : ℚ :=
  r*(r-1)*(r-2401)*(32*r+343)*(2*r-1)

theorem phi_at_one : phi 1=3 := by norm_num [phi]

theorem contacts_at_three :
    (3 : ℚ)-1=2 ∧ (3 : ℚ)-2401 = -2398 ∧
    32*(3 : ℚ)+343=439 ∧ 2*(3 : ℚ)-1=5 := by norm_num

theorem no_large_prime_contact (p : ℕ) (hp : p.Prime) (hlarge : 76176 < p) :
    ¬ p ∣ 3*2*2398*439*5 := by
  intro hd
  have small (n : ℕ) (hn : 0<n) (hbound : n≤76176) : ¬ p ∣ n := by
    intro h
    have := Nat.le_of_dvd hn h
    omega
  simp only [hp.dvd_mul] at hd
  rcases hd with (((h|h)|h)|h)|h
  · exact small 3 (by norm_num) (by norm_num) h
  · exact small 2 (by norm_num) (by norm_num) h
  · exact small 2398 (by norm_num) (by norm_num) h
  · exact small 439 (by norm_num) (by norm_num) h
  · exact small 5 (by norm_num) (by norm_num) h

theorem product_numerator_at_one :
    (contactProduct (phi 1)).num.natAbs=3*2*2398*439*5 := by
  norm_num [phi,contactProduct]

theorem no_large_prime_at_degenerate_parameter
    (p : ℕ) (hp : p.Prime) (hlarge : 76176<p) :
    ¬ p ∣ (contactProduct (phi 1)).num.natAbs := by
  rw [product_numerator_at_one]
  exact no_large_prime_contact p hp hlarge
end DegenerateContacts
