module
public import OriginalPhysicalHZ210Map318
public import OriginalRadixHZCertificate318
public section
namespace OriginalPhysicalHZ210Identity318
open OriginalPhysicalHZ210Coefficients318 OriginalMarkedIntPolynomialCertificate318 OriginalRadixHZCertificate318
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

@[expose] def pw (f : E) : ℕ → E
  | 0 => .p [1]
  | n+1 => .mul (pw f n) f
@[expose] def wz (t : Term) : E :=
  .scale t.coeff (.mul (.mul (pw (.p A) t.i) (pw (.p B) t.j)) (pw (.p C) t.k))
@[expose] def wsum : List Term → E
  | [] => .p []
  | t :: l => .add (wz t) (wsum l)
theorem ev_pw {R : Type*} [CommRing R] (z : R) (f : E) (n : ℕ) :
    Ev z (pw f n) = (Ev z f)^n := by
  induction n with
  | zero => simp [pw,Ev,horner]
  | succ n ih => simp only [pw,Ev,ih,pow_succ]
theorem horner_eq {R : Type*} [CommRing R] (z : R) (l : List ℤ) :
    horner z l = OriginalPhysicalHZ210Map318.horner z l := by
  induction l with
  | nil => rfl
  | cons h l ih => simp only [horner,OriginalPhysicalHZ210Map318.horner,ih]
theorem ev_wsum {R : Type*} [CommRing R] (z : R) (l : List Term) :
    Ev z (wsum l) = OriginalPhysicalHZ210Map318.form (OriginalPhysicalHZ210Map318.horner z A) (OriginalPhysicalHZ210Map318.horner z B) (OriginalPhysicalHZ210Map318.horner z C) l := by
  induction l with
  | nil => rfl
  | cons t l ih => simp only [wsum, wz, Ev, ev_pw, horner_eq, ih, OriginalPhysicalHZ210Map318.form, OriginalPhysicalHZ210Map318.val]

theorem cap_pw (f : E) (n : ℕ) : cap (pw f n)=(cap f)^n := by
  induction n with
  | zero => simp [pw,cap,mass]
  | succ n ih => simp only [pw,cap,ih,pow_succ]
@[expose] def boundTerms : List Term → ℕ
  | [] => 0
  | t::l => t.coeff.natAbs * (92^t.i*8667534^t.j*527967161176^t.k) + boundTerms l
theorem cap_wsum (l : List Term) : cap (wsum l) = boundTerms l := by
  have ha : mass A=92 := by decide
  have hb : mass B=8667534 := by decide
  have hc : mass C=527967161176 := by decide
  induction l with
  | nil => rfl
  | cons t l ih => simp only [wsum,wz,cap,cap_pw,ih,ha,hb,hc,boundTerms]

theorem bound : boundTerms terms < 2^841 := by decide +kernel

theorem at_radix : OriginalPhysicalHZ210Map318.physical (((2:ℕ)^841:ℕ):ℤ)=0 := by decide +kernel

/-- True 139-monomial HZ210 identity on the literal physical weighted coordinate
polynomials. In particular this is an identity in ℤ[X] and in every residue field. -/
theorem all_rings {R : Type*} [CommRing R] (z : R) : OriginalPhysicalHZ210Map318.physical z = 0 := by
  have h : cap (wsum terms) < 2^841 := (cap_wsum terms) ▸ bound
  have hv : Ev (((2:ℕ)^841:ℕ):ℤ) (wsum terms) = 0 := (ev_wsum _ terms).trans at_radix
  exact (ev_wsum z terms).symm.trans (certificate z (2^841) (wsum terms) h hv)

theorem polynomial_identity : OriginalPhysicalHZ210Map318.physical (Polynomial.X : Polynomial ℤ) = 0 := all_rings _
end OriginalPhysicalHZ210Identity318
#print axioms OriginalPhysicalHZ210Identity318.all_rings
#print axioms OriginalPhysicalHZ210Identity318.polynomial_identity
