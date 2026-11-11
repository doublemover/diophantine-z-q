module
public import ValuativeOrbitBounds318
public section
noncomputable section
namespace ValuativeOrbitMultiples318
open ValuativeOrbitBounds318
open ConcreteG8Domain (K D)
open CoherentMultipleCharts318 (chartU chartV)
set_option maxHeartbeats 1000000
variable (v : AddValuation K (WithTop ℤ))

lemma near_zero (r : ℤ) : Near v r (chartU 0) (chartV 0) := by
  simp [Near,Bound]
lemma near_neg (r N : ℤ) (hN : Near v r (chartU N) (chartV N)) :
    Near v r (chartU (-N)) (chartV (-N)) := by
  simpa only [CoherentMultipleCharts318.chartU_negative,CoherentMultipleCharts318.chartV_negative]
    using And.intro (bneg v hN.1) hN.2

lemma near_nat (r N : ℤ) (hr : 1≤r) (hD : Bound v 0 D)
    (hN : Near v r (chartU N) (chartV N)) (n : ℕ) :
    Near v r (chartU ((n:ℤ)*N)) (chartV ((n:ℤ)*N)) := by
  induction n with
  | zero => simpa only [Nat.cast_zero,zero_mul] using near_zero v r
  | succ n ih =>
    rw [show ((n+1:ℕ):ℤ)*N=(n:ℤ)*N+N by push_cast; ring,
      CoherentAdditionV318.chartU_add,CoherentAdditionV318.chartV_add]
    exact addition_near v D _ _ _ _ r hr hD ih hN

lemma near_int (r N : ℤ) (hr : 1≤r) (hD : Bound v 0 D)
    (hN : Near v r (chartU N) (chartV N)) (n : ℤ) :
    Near v r (chartU (n*N)) (chartV (n*N)) := by
  rcases le_total 0 n with hn|hn
  · have he : (n.natAbs:ℤ)=n := by rw [Int.natCast_natAbs,abs_of_nonneg hn]
    simpa only [he] using near_nat v r N hr hD hN n.natAbs
  · have he : (n.natAbs:ℤ)= -n := by rw [Int.natCast_natAbs,abs_of_nonpos hn]
    have hm := near_neg v r ((n.natAbs:ℤ)*N) (near_nat v r N hr hD hN n.natAbs)
    simpa only [he,neg_mul,neg_neg] using hm

/-- Actual multiples agree with scalar multiplication to second order in
both oriented reciprocal coordinates. Identity multiples are included. -/
theorem linear_multiple (r N : ℤ) (hr : 1≤r) (hD : Bound v 0 D)
    (hN : Near v r (chartU N) (chartV N)) (n : ℕ) :
    Bound v (2*r) (chartU ((n:ℤ)*N)-(n:K)*chartU N) ∧
    Bound v (2*r) (chartV ((n:ℤ)*N)-1-(n:K)*(chartV N-1)) := by
  induction n with
  | zero => simp [Bound]
  | succ n ih =>
    have hn := near_nat v r N hr hD hN n
    obtain ⟨heU,heV⟩ := addition_errors v D (chartU ((n:ℤ)*N))
      (chartV ((n:ℤ)*N)) (chartU N) (chartV N) r hr hD hn hN
    rw [←CoherentAdditionV318.chartU_add] at heU
    rw [←CoherentAdditionV318.chartV_add] at heV
    have hindex : ((n+1:ℕ):ℤ)*N=(n:ℤ)*N+N := by push_cast; ring
    rw [hindex]
    constructor
    · have he := badd v heU ih.1
      convert he using 1 <;> push_cast <;> ring
    · have he := badd v heV ih.2
      convert he using 1 <;> push_cast <;> ring

/-- Multiplication by any integer whose valuation is at least one raises
positive chart precision. This does not use a p-adic logarithm theorem. -/
theorem prime_step (p : ℕ) (hp : Bound v 1 (p:K))
    (r N : ℤ) (hr : 1≤r) (hD : Bound v 0 D)
    (hN : Near v r (chartU N) (chartV N)) :
    Near v (r+1) (chartU ((p:ℤ)*N)) (chartV ((p:ℤ)*N)) := by
  obtain ⟨heU,heV⟩ := linear_multiple v r N hr hD hN p
  have hu : Bound v (r+1) ((p:K)*chartU N) := by
    simpa only [add_comm] using bmul v hp hN.1
  have hv : Bound v (r+1) ((p:K)*(chartV N-1)) := by
    simpa only [add_comm] using bmul v hp hN.2
  constructor
  · have he := badd v (weaken v heU (by omega)) hu
    simpa only [sub_add_cancel] using he
  · have he := badd v (weaken v heV (by omega)) hv
    simpa only [sub_add_cancel] using he

/-- One genuine entry point supplies unbounded local precision, uniformly
for every later signed multiplier of the resulting explicit modulus. -/
theorem prime_power_multiples (p : ℕ) (hp : Bound v 1 (p:K))
    (N : ℤ) (hD : Bound v 0 D) (hN : Near v 1 (chartU N) (chartV N))
    (e : ℕ) (m : ℤ) :
    Near v ((e:ℤ)+1) (chartU ((p:ℤ)^e*N*m)) (chartV ((p:ℤ)^e*N*m)) := by
  have he : ∀ e : ℕ, Near v ((e:ℤ)+1)
      (chartU ((p:ℤ)^e*N)) (chartV ((p:ℤ)^e*N)) := by
    intro e
    induction e with
    | zero => simpa using hN
    | succ e ih =>
      have hs := prime_step v p hp ((e:ℤ)+1) ((p:ℤ)^e*N) (by omega) hD ih
      have hi : (p:ℤ)^(e+1)*N=(p:ℤ)*((p:ℤ)^e*N) := by rw [pow_succ]; ring
      rw [hi]
      simpa only [Nat.cast_add,Nat.cast_one] using hs
  simpa only [mul_comm m] using near_int v ((e:ℤ)+1) ((p:ℤ)^e*N) (by omega) hD (he e) m

end ValuativeOrbitMultiples318
