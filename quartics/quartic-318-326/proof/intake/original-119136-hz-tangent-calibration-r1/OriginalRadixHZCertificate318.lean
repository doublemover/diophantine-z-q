module
public import OriginalMarkedIntPolynomialCertificate318
public section
namespace OriginalRadixHZCertificate318
open OriginalMarkedIntPolynomialCertificate318
@[expose] def mass : List ℤ → ℕ
  | [] => 0
  | h::t => h.natAbs + mass t
theorem mass_plus (p q : List ℤ) : mass (plus p q) ≤ mass p + mass q := by
  induction p generalizing q with
  | nil => simp [plus,mass]
  | cons h p hp =>
    cases q with
    | nil => simp [plus,mass]
    | cons g q =>
      simp only [plus,mass]
      have := Int.natAbs_add_le h g
      have := hp q
      omega
theorem mass_scal (n : ℤ) (p : List ℤ) : mass (scal n p) = n.natAbs * mass p := by
  induction p with
  | nil => simp [scal,mass]
  | cons h p hp =>
    change (n*h).natAbs + mass (scal n p) = n.natAbs*(h.natAbs+mass p)
    rw [Int.natAbs_mul, hp, Nat.mul_add]
theorem mass_times (p q : List ℤ) : mass (times p q) ≤ mass p * mass q := by
  induction p with
  | nil => simp [times,mass]
  | cons h p hp =>
    apply (mass_plus _ _).trans
    rw [mass_scal, mass, Int.natAbs_zero, Nat.zero_add, mass, Nat.add_mul]
    exact Nat.add_le_add_left hp _
@[expose] def cap : E → ℕ
  | .p l => mass l
  | .add a b => cap a + cap b
  | .mul a b => cap a * cap b
  | .scale c a => c.natAbs * cap a
theorem cap_bound (f : E) : mass (expand f) ≤ cap f := by
  induction f with
  | p _ => rfl
  | add a b ha hb => exact (mass_plus ..).trans (Nat.add_le_add ha hb)
  | mul a b ha hb => exact (mass_times ..).trans (Nat.mul_le_mul ha hb)
  | scale c a ha => exact (mass_scal c _).le.trans (Nat.mul_le_mul_left _ ha)
theorem zero_of_radix {n : ℕ} (l : List ℤ) (h : mass l < n) (hv : horner (n:ℤ) l=0) :
    l.all (fun a => a == 0)=true := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    change a.natAbs + mass l < n at h
    change (a:ℤ) + (n:ℤ)*horner (n:ℤ) l = 0 at hv
    have hd : (n:ℤ) ∣ a := ⟨-horner (n:ℤ) l,by linarith⟩
    have hd' : n ∣ a.natAbs := by simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr hd
    have ha : a = 0 := by
      by_contra hn
      have hp : 0 < a.natAbs := Int.natAbs_pos.mpr hn
      have := Nat.le_of_dvd hp hd'
      omega
    subst a
    have hn : n ≠ 0 := by omega
    have hv' : horner (n:ℤ) l=0 := by simpa [hn] using hv
    simp [ih (by simpa using h) hv']
theorem certificate {R : Type*} [CommRing R] (z : R) (n : ℕ) (f : E)
    (hb : cap f < n) (h : Ev (n:ℤ) f = 0) : Ev z f = 0 := by
  apply sound
  apply zero_of_radix (n:=n)
  · exact (cap_bound f).trans_lt hb
  · simpa only [ev_eq] using h
end OriginalRadixHZCertificate318
