module
public import ActualQuarterDenominatorCoverage318
public import PrimeCRTAssembly
public section
namespace ExactContinuityDivisibilityCRT318
/-- With the other historical coprimalities retained, the EXACT continuity requirement
is gcd(Pi^e*Mminus,L)|h0. No extraneous equality to16 is needed. Zero moduli are allowed. -/
theorem compatible_iff (Pi Mminus Mplus L h0 e : ℕ)
    (hPm : Nat.Coprime Pi Mplus) (hmp : Nat.Coprime Mminus Mplus)
    (hpL : Nat.Coprime Mplus L) :
    (∃ h : ℕ, Nat.ModEq (Pi^e*Mminus) h 0 ∧ Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h0) ↔
      Nat.gcd (Pi^e*Mminus) L∣h0 := by
  constructor
  · rintro ⟨h,hA,hP,hL⟩
    have he := (hA.of_dvd (Nat.gcd_dvd_left (Pi^e*Mminus) L)).symm.trans
      (hL.of_dvd (Nat.gcd_dvd_right (Pi^e*Mminus) L))
    exact Nat.modEq_zero_iff_dvd.mp he.symm
  · intro hd
    let A := Pi^e*Mminus
    have hc : Nat.ModEq (Nat.gcd A L) 0 h0 := hd.modEq_zero_nat.symm
    let h1 := Nat.chineseRemainder' hc
    have hcop : Nat.Coprime (A*L) Mplus :=
      ((hPm.pow_left e).mul_left hmp).mul_left hpL.symm
    let h2 := Nat.chineseRemainder hcop h1.val 1
    exact ⟨h2.val,(h2.property.1.of_dvd (dvd_mul_right A L)).trans h1.property.1,
      h2.property.2,(h2.property.1.of_dvd (dvd_mul_left L A)).trans h1.property.2⟩
/-- Positivity allows arbitrary size after compatibility, but supplies no orbit-region hit. -/
theorem arbitrarily_large (Pi Mminus Mplus L h0 e B : ℕ)
    (hPi : 0<Pi) (hm : 0<Mminus) (hp : 0<Mplus) (hL : 0<L)
    (hPm : Nat.Coprime Pi Mplus) (hmp : Nat.Coprime Mminus Mplus)
    (hpL : Nat.Coprime Mplus L) (hc : Nat.gcd (Pi^e*Mminus) L∣h0) :
    ∃ h : ℕ, B<h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧ Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h0 := by
  obtain ⟨h,hA,hP,hL'⟩ := (compatible_iff Pi Mminus Mplus L h0 e hPm hmp hpL).mpr hc
  let D := Pi^e*Mminus*Mplus*L
  have hD : 0<D := by dsimp [D];positivity
  have shift (n : ℕ) (hn : n∣D) : Nat.ModEq n (h+D*(B+1)) h := by
    have hd : n∣D*(B+1) := dvd_mul_of_dvd_left hn _
    simp [Nat.ModEq,Nat.add_mod,Nat.mod_eq_zero_of_dvd hd]
  refine ⟨h+D*(B+1),?_,?_,?_,?_⟩
  · have h1 : 1≤D := hD
    have he:=Nat.mul_le_mul_right (B+1) h1
    omega
  · exact (shift _ ⟨Mplus*L,by dsimp [D];ring⟩).trans hA
  · exact (shift _ ⟨Pi^e*Mminus*L,by dsimp [D];ring⟩).trans hP
  · exact (shift _ ⟨Pi^e*Mminus*Mplus,by dsimp [D];ring⟩).trans hL'
end ExactContinuityDivisibilityCRT318
