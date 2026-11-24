module
public import OriginalPhysicalNaganoFirstJet318
public section
namespace OriginalUniformFractionCert318
open OriginalMarkedIntPolynomialCertificate318 OriginalRadixHZCertificate318 OriginalPhysicalHZ210Identity318

/-! Homogeneous multivariate gate certificates specialized to one integer-polynomial parameter. -/
abbrev PairE := E × E
abbrev Mono := List (ℕ × ℕ)
abbrev Term := ℤ × Mono
@[expose] def mono : List PairE → Mono → E
  | (a,b)::xs,(i,j)::ms => .mul (.mul (pw a i) (pw b j)) (mono xs ms)
  | _,_ => .p [1]
@[expose] def expr (xs : List PairE) : List Term → E
  | [] => .p []
  | (c,m)::ms => .add (.scale c (mono xs m)) (expr xs ms)
@[expose] def ratios {K : Type*} [Field K] (z : K) (xs : List PairE) : List K :=
  xs.map (fun p => Ev z p.1 / Ev z p.2)
@[expose] def mno {K : Type*} [Field K] : List K → Mono → K
  | a::xs,(i,_)::ms => a^i * mno xs ms
  | _,_ => 1
@[expose] def value {K : Type*} [Field K] (xs : List K) : List Term → K
  | [] => 0
  | (c,m)::ms => c * mno xs m + value xs ms
@[expose] def dens {K : Type*} [Field K] (z : K) : List PairE → List ℕ → K
  | (_,b)::xs,d::ds => (Ev z b)^d * dens z xs ds
  | _,_ => 1
@[expose] def degreeVec (m : Mono) : List ℕ := m.map fun a => a.1+a.2
@[expose] def valid (ds : List ℕ) (ts : List Term) : Bool := ts.all fun t => degreeVec t.2 == ds

theorem mono_sound {K : Type*} [Field K] (z : K) (xs : List PairE) (m : Mono)
    (hn : ∀ p ∈ xs, Ev z p.2 ≠ 0) :
    Ev z (mono xs m)=mno (ratios z xs) m * dens z xs (degreeVec m) := by
  induction xs generalizing m with
  | nil => cases m <;> simp [mono,Ev,horner,mno,ratios,dens]
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    cases m with
    | nil => simp [mono,Ev,horner,mno,ratios,dens,degreeVec]
    | cons ij m =>
      rcases ij with ⟨i,j⟩
      have hb := hn (a,b) (by simp)
      have ht : ∀ p ∈ xs, Ev z p.2 ≠ 0 := fun p h => hn p (by simp [h])
      have h := ih m ht
      simp only [mono,Ev,ev_pw,ratios,List.map_cons,mno,degreeVec,dens] at h ⊢
      rw [h,div_pow,pow_add]
      field_simp

theorem expr_sound {K : Type*} [Field K] (z : K) (xs : List PairE) (ds : List ℕ) (ts : List Term)
    (hn : ∀ p ∈ xs, Ev z p.2 ≠ 0) (ht : valid ds ts = true) :
    Ev z (expr xs ts)=value (ratios z xs) ts * dens z xs ds := by
  induction ts with
  | nil => simp [expr,Ev,horner,value]
  | cons t ts ih =>
    rcases t with ⟨c,m⟩
    simp only [valid,List.all_cons,Bool.and_eq_true,beq_iff_eq] at ht
    simp only [expr,Ev,value]
    rw [mono_sound z xs m hn,ht.1,ih ht.2]
    ring

theorem dens_ne {K : Type*} [Field K] (z : K) (xs : List PairE) (ds : List ℕ)
    (hn : ∀ p ∈ xs, Ev z p.2 ≠ 0) : dens z xs ds ≠ 0 := by
  induction xs generalizing ds with
  | nil => simp [dens]
  | cons x xs ih =>
    rcases x with ⟨a,b⟩
    cases ds with
    | nil => simp [dens]
    | cons i ds => exact mul_ne_zero (pow_ne_zero _ (hn (a,b) (by simp))) (ih ds (fun p h => hn p (by simp [h])))

theorem certify {K : Type*} [Field K] (z : K) (xs : List PairE) (ds : List ℕ) (ts : List Term)
    (hn : ∀ p ∈ xs, Ev z p.2 ≠ 0) (ht : valid ds ts = true) (n : ℕ)
    (hb : cap (expr xs ts)<n) (hv : Ev (n:ℤ) (expr xs ts)=0) :
    value (ratios z xs) ts=0 := by
  have h := certificate z n (expr xs ts) hb hv
  rw [expr_sound z xs ds ts hn ht] at h
  exact (mul_eq_zero.mp h).resolve_right (dens_ne z xs ds hn)

end OriginalUniformFractionCert318
#print axioms OriginalUniformFractionCert318.certify
