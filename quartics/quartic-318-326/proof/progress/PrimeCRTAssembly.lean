module
public import Height13RealLog
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Algebra.GCDMonoid.Finset
public section
namespace PrimeCRTAssembly

/-- Passing from individual opposite orders to the lcm of their doubling-image
orders does not create a selected-prime divisor. The `r ∣ d` premise is realized
by `r = d / 4` and the full rational two-torsion condition `4 ∣ d`. -/
theorem product_coprime_lcm {ι κ : Type*} (S : Finset ι) (T : Finset κ)
    (p : ι → ℕ) (d r : κ → ℕ)
    (hp : ∀ i ∈ S, Nat.Prime (p i))
    (hsep : ∀ i ∈ S, ∀ j ∈ T, ¬ p i ∣ d j)
    (hr : ∀ j ∈ T, r j ∣ d j) :
    Nat.Coprime (S.prod p) (T.lcm r) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro i hi
  have hpR : Nat.Coprime (p i) (T.prod r) := by
    apply Nat.coprime_prod_right_iff.mpr
    intro j hj
    apply (hp i hi).coprime_iff_not_dvd.mpr
    intro hd
    exact hsep i hi j hj (hd.trans (hr j hj))
  apply hpR.of_dvd_right
  exact T.lcm_dvd (fun j hj => Finset.dvd_prod_of_mem r hj)

/-- Source CRT assembly: the extra primary exponent may be any natural e.
Only the prime-pattern coprimalities and 16-divisibility of h₀ are used. -/
theorem compatible_primary_depth
    (Pi Mminus Mplus L h₀ e : ℕ)
    (hPm : Nat.Coprime Pi Mplus) (hPL : Nat.Coprime Pi L)
    (hmp : Nat.Coprime Mminus Mplus)
    (hpL : Nat.Coprime Mplus L)
    (hmL : Nat.gcd Mminus L = 16) (hh₀ : 16 ∣ h₀) :
    ∃ h : ℕ, Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ := by
  let A := Pi^e*Mminus
  have hAL : Nat.gcd A L = 16 := by
    dsimp [A]
    rw [Nat.Coprime.gcd_mul_left_cancel Mminus (hPL.pow_left e), hmL]
  have hcompat : Nat.ModEq (Nat.gcd A L) 0 h₀ := by
    rw [hAL]
    exact hh₀.modEq_zero_nat.symm
  let h1 := Nat.chineseRemainder' hcompat
  have haPlus : Nat.Coprime (A*L) Mplus :=
    ((hPm.pow_left e).mul_left hmp).mul_left hpL.symm
  let h2 := Nat.chineseRemainder haPlus h1.val 1
  refine ⟨h2.val, ?_, h2.property.2, ?_⟩
  · exact (h2.property.1.of_dvd (dvd_mul_right A L)).trans h1.property.1
  · exact (h2.property.1.of_dvd (dvd_mul_left L A)).trans h1.property.2

/-- The three congruences allow arbitrarily large positive indices. Density in
 the real elliptic orbit is a separate topological input, not asserted here. -/
theorem arbitrarily_large_primary_depth
    (Pi Mminus Mplus L h₀ e B : ℕ)
    (hPi : 0 < Pi) (hMm : 0 < Mminus) (hMp : 0 < Mplus) (hL : 0 < L)
    (hPm : Nat.Coprime Pi Mplus) (hPL : Nat.Coprime Pi L)
    (hmp : Nat.Coprime Mminus Mplus)
    (hpL : Nat.Coprime Mplus L)
    (hmL : Nat.gcd Mminus L = 16) (hh₀ : 16 ∣ h₀) :
    ∃ h : ℕ, B < h ∧ Nat.ModEq (Pi^e*Mminus) h 0 ∧
      Nat.ModEq Mplus h 1 ∧ Nat.ModEq L h h₀ := by
  obtain ⟨h, hhA, hhP, hhL⟩ :=
    compatible_primary_depth Pi Mminus Mplus L h₀ e hPm hPL hmp hpL hmL hh₀
  let D := Pi^e*Mminus*Mplus*L
  have hD : 0<D := by dsimp [D]; positivity
  have hshift (n : ℕ) (hn : n∣D) : Nat.ModEq n (h+D*(B+1)) h := by
    have hdiv : n ∣ D*(B+1) := dvd_mul_of_dvd_left hn _
    simp [Nat.ModEq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv]
  refine ⟨h+D*(B+1), ?_, ?_, ?_, ?_⟩
  · have hd1 : 1≤D := hD
    have hz := Nat.mul_le_mul_right (B+1) hd1
    omega
  · apply (hshift (Pi^e*Mminus) ?_).trans hhA
    exact ⟨Mplus*L, by dsimp [D]; ring⟩
  · apply (hshift Mplus ?_).trans hhP
    exact ⟨Pi^e*Mminus*L, by dsimp [D]; ring⟩
  · apply (hshift L ?_).trans hhL
    exact ⟨Pi^e*Mminus*Mplus, by dsimp [D]; ring⟩

/-- The current source's factor 64 also kills the component of R₀, even
when the component order was originally measured using P=2R₀. Thus keeping
h≡h₀ mod L does not accidentally move the coherent square-root charts to
the other real component. Density inside that component is separate. -/
theorem coherent_component_compatibility {C : Type*} [AddCommGroup C]
    (R₀ : C) (m h L h₀ : ℕ)
    (hcomp : m • (2 • R₀)=0)
    (hL : 64*m ∣ L) (hh₀ : 64*m ∣ h₀)
    (hh : Nat.ModEq L h h₀) : h • R₀=0 := by
  have hkill : (64*m) • R₀=0 := by
    calc
      (64*m) • R₀ = 32 • (m • (2 • R₀)) := by
        simp only [← mul_nsmul]
        congr 1
        ring
      _ = 0 := by rw [hcomp]; simp
  have hd : 64*m ∣ h := Nat.modEq_zero_iff_dvd.mp
    ((hh.of_dvd hL).trans hh₀.modEq_zero_nat)
  obtain ⟨n, hn⟩ := hd
  rw [hn, mul_nsmul, hkill, nsmul_zero]

#print axioms product_coprime_lcm
#print axioms compatible_primary_depth
#print axioms arbitrarily_large_primary_depth
#print axioms coherent_component_compatibility
end PrimeCRTAssembly
