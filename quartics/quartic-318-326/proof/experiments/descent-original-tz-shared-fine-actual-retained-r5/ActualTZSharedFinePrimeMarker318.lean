module
public import ActualTZSharedFineHybridProbes318
public section
noncomputable section
namespace ActualTZSharedFinePrimeMarker318
open ActualTZSharedFineHybridStencil318 ActualTZSharedFineHybridProbes318
open ActualTZProbeExceptionalWheel318

variable {a t b s : ℕ}

private theorem local_not_dvd (W q p D : ℕ) (hp : p.Prime) (hD : D<p)
    (hP : ¬p∣W*q) (c : ℤ) (hc : c≠0) (hC : c.natAbs≤D) :
    ¬(p:ℤ)∣(W:ℤ)*((W:ℤ)*c) := by
  have hW : ¬p∣W := fun h=>hP (dvd_mul_of_dvd_left h _)
  have hc' : ¬p∣c.natAbs := by
    intro hz
    have h0 := Int.natAbs_pos.mpr hc
    have h := Nat.le_of_dvd h0 hz
    omega
  intro hz
  have h : p∣((W:ℤ)*((W:ℤ)*c)).natAbs := by
    rw [←Int.natCast_dvd_natCast,Int.dvd_natAbs]
    exact hz
  simp only [Int.natAbs_mul,Int.natAbs_natCast] at h
  rcases hp.dvd_mul.1 h with h|h
  · exact hW h
  rcases hp.dvd_mul.1 h with h|h
  · exact hW h
  · exact hc' h

/-- Actual multi-axis hybrid marker at distinct vertices. The
same h_r enters every local direction in whole test r. The
selected endpoint coordinate isolates one old nonzero divided
coefficient even when all other rows depend on that same h_r. -/
theorem survives (W n q p D : ℕ) (hp : p.Prime) (hD : D<p) (hP : ¬p∣W*q)
    (c : Fin b→Fin s→ℤ) (hRow : ∀ j,∃ k,c j k≠0 ∧ (c j k).natAbs≤D)
    (w v : Bits a t b) (h : w≠v) (e f : ℤ) :
    MvPolynomial.map (Int.castRingHom (ZMod p))
      (physical W n q (fun j k=>(W:ℤ)*c j k) w v e f)≠0 := by
  classical
  have hd : ∃ i,w i≠v i := by
    by_contra! hNo
    exact h (funext hNo)
  obtain ⟨i,hi⟩ := hd
  let A (j : Fin b) (k : Fin s) := (W:ℤ)*c j k
  have hG : ¬(p:ℤ)∣(W:ℤ)*(q:ℤ) := by exact_mod_cast hP
  change MvPolynomial.map (Int.castRingHom (ZMod p)) (physical W n q A w v e f)≠0
  cases i with
  | inl i =>
    apply nonzero_from_probe p _ (globalNeedle i) (fun _=>0)
    rw [eval_physical W n q A w v e f 0 0 (globalNeedle i),
      eval_physical W n q A w v e f 0 0 (fun _=>0)]
    simp only [ActualTZSharedFineHybridProbes318.global,ActualTZSharedFineHybridProbes318.zero]
    cases hw : w (.inl i) <;> cases hv : v (.inl i)
    · exact (hi (hw.trans hv.symm)).elim
    · simp only [hw,hv,Bool.false_eq_true,if_false,if_true]
      convert (fun H=>hG (dvd_neg.mp H) : ¬(p:ℤ)∣-((W:ℤ)*(q:ℤ))) using 1 <;> ring
    · simp only [hw,hv,Bool.false_eq_true,if_false,if_true]
      convert hG using 1 <;> ring
    · exact (hi (hw.trans hv.symm)).elim
  | inr i =>
    obtain ⟨k,hK,hKC⟩ := hRow i.2
    have hL : ¬(p:ℤ)∣(W:ℤ)*(A i.2 k) := local_not_dvd W q p D hp hD hP _ hK hKC
    apply nonzero_from_probe p _ (localNeedle i.1 i.2 k) (fun _=>0)
    rw [eval_physical W n q A w v e f 0 0 (localNeedle i.1 i.2 k),
      eval_physical W n q A w v e f 0 0 (fun _=>0)]
    simp only [local_axis,ActualTZSharedFineHybridProbes318.zero]
    cases hw : w (.inr i) <;> cases hv : v (.inr i)
    · exact (hi (hw.trans hv.symm)).elim
    · simp only [hw,hv,Bool.false_eq_true,if_false,if_true]
      convert (fun H=>hL (dvd_neg.mp H) : ¬(p:ℤ)∣-((W:ℤ)*A i.2 k)) using 1 <;> ring
    · simp only [hw,hv,Bool.false_eq_true,if_false,if_true]
      convert hL using 1 <;> ring
    · exact (hi (hw.trans hv.symm)).elim

end ActualTZSharedFinePrimeMarker318
