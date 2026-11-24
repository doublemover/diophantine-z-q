module
public import OriginalPhysicalHZ210Coefficients318
public section
namespace OriginalMarkedIntPolynomialCertificate318
@[expose] def horner {R : Type*} [CommRing R] (z : R) : List ℤ → R
  | [] => 0
  | c :: l => (c : R) + z * horner z l
@[expose] def plus : List ℤ → List ℤ → List ℤ
  | [], ys => ys
  | xs, [] => xs
  | a::xs, b::ys => (a+b)::plus xs ys
@[expose] def scal (q : ℤ) (xs : List ℤ) := xs.map (q * ·)
@[expose] def times : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | a::l, b => plus (scal a b) (0::times l b)
theorem horner_plus {R : Type*} [CommRing R] (z : R) (p q : List ℤ) :
    horner z (plus p q) = horner z p + horner z q := by
  induction p generalizing q with
  | nil => simp [plus, horner]
  | cons a p hp =>
    cases q with
    | nil => simp [plus, horner]
    | cons b q => simp only [plus, horner, Int.cast_add, hp]; ring
theorem horner_scal {R : Type*} [CommRing R] (z : R) (n : ℤ) (p : List ℤ) :
    horner z (scal n p) = n * horner z p := by
  induction p with
  | nil => simp [scal, horner]
  | cons a p hp =>
    change ((n*a:ℤ):R) + z * horner z (scal n p) = (n:R) * ((a:R) + z*horner z p)
    rw [Int.cast_mul, hp]; ring
theorem horner_times {R : Type*} [CommRing R] (z : R) (p q : List ℤ) :
    horner z (times p q) = horner z p * horner z q := by
  induction p with
  | nil => simp [times, horner]
  | cons a p hp => simp only [times, horner_plus, horner_scal, horner, Int.cast_zero, zero_add, hp]; ring
inductive E where
  | p (l : List ℤ)
  | add (a b : E)
  | mul (a b : E)
  | scale (c : ℤ) (a : E)
@[expose] def Ev {R : Type*} [CommRing R] (z : R) : E → R
  | .p l => horner z l
  | .add a b => Ev z a + Ev z b
  | .mul a b => Ev z a * Ev z b
  | .scale c a => c * Ev z a
@[expose] def expand : E → List ℤ
  | .p l => l
  | .add a b => plus (expand a) (expand b)
  | .mul a b => times (expand a) (expand b)
  | .scale c a => scal c (expand a)
theorem ev_eq {R : Type*} [CommRing R] (z : R) (f : E) : Ev z f = horner z (expand f) := by
  induction f with
  | p l => rfl
  | add a b ha hb => rw [Ev, expand, horner_plus, ha, hb]
  | mul a b ha hb => rw [Ev, expand, horner_times, ha, hb]
  | scale c a ha => rw [Ev, expand, horner_scal, ha]
@[expose] def zeroTest (f : E) : Bool := (expand f).all fun k => k == 0
theorem sound {R : Type*} [CommRing R] (z : R) {f : E} (h : zeroTest f = true) : Ev z f = 0 := by
  rw [ev_eq]
  suffices hh : ∀ (l : List ℤ), (l.all fun n => n == 0) = true → horner z l = 0 from hh _ h
  intro l; induction l with
  | nil => intro _; rfl
  | cons a l ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at *
    rintro ⟨rfl,h⟩
    simp [horner, ih h]
end OriginalMarkedIntPolynomialCertificate318
