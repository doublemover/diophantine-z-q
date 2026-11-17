module
public import AuxiliaryBadPrimeResidues318
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public section
namespace AuxiliaryLocalCharacters318

private theorem cast_ne (p : ℕ) [Fact p.Prime] (a : ℤ) (ha : ¬(p:ℤ)∣a) :
    (a:ZMod p)≠0 := fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)

private theorem jacobi_square_one (p : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : (a:ZMod p)≠0) : jacobiSym a p^2=1 := by
  rw [←jacobiSym.legendreSym.to_jacobiSym p a]
  exact legendreSym.sq_one p ha

private theorem jacobi_one_of_square (p : ℕ) [Fact p.Prime] (a : ℤ)
    (ha : (a:ZMod p)≠0) (hs : IsSquare (a:ZMod p)) : jacobiSym a p=1 := by
  rw [←jacobiSym.legendreSym.to_jacobiSym p a]
  exact (legendreSym.eq_one_iff p ha).mpr hs

/-- A nonzero modular square ratio gives equality of the two characters.
Both modular nonzero conditions are retained rather than inferring Jacobi1
from a possibly zero square. -/
theorem character_eq_of_square_ratio (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (ha : (a:ZMod p)≠0) (hb : (b:ZMod p)≠0)
    (hs : IsSquare ((a:ZMod p)/(b:ZMod p))) : jacobiSym a p=jacobiSym b p := by
  obtain ⟨r,hr⟩ := hs
  have hab : (a:ZMod p)=r*r*(b:ZMod p) := (div_eq_iff hb).mp hr
  have hsprod : IsSquare ((a*b:ℤ):ZMod p) := by
    refine ⟨r*(b:ZMod p),?_⟩
    push_cast
    rw [hab]
    ring
  have hj := jacobi_one_of_square p (a*b) (by simpa only [Int.cast_mul] using mul_ne_zero ha hb) hsprod
  rw [jacobiSym.mul_left] at hj
  have hb2 := jacobi_square_one p b hb
  calc
    jacobiSym a p=jacobiSym a p*(jacobiSym b p)^2 := by rw [hb2,mul_one]
    _=(jacobiSym a p*jacobiSym b p)*jacobiSym b p := by ring
    _=jacobiSym b p := by rw [hj,one_mul]

/-- At a selected coefficient prime, the actual B representation yields the
precise character identity needed by the global product. R is the remaining
selected product after removing p; its unit condition is explicit. -/
theorem selected_identity (p : ℕ) [Fact p.Prime] (ε σ R U q : ℤ) (α : ℕ)
    (hε : ε=1 ∨ ε= -1) (hσ : σ=1 ∨ σ= -1)
    (h6 : ¬(p:ℤ)∣6) (hR : ¬(p:ℤ)∣R) (hU : ¬(p:ℤ)∣U) (hq : ¬(p:ℤ)∣q)
    (h2 : jacobiSym 2 p=1) (T Y : ℚ_[p])
    (hB : (((p:ℤ)*(ε*R*U):ℤ):ℚ_[p])*T^2-6*Y^2=
      (((p:ℤ)*(σ*2^α*R*q):ℤ):ℚ_[p])) :
    jacobiSym q p=jacobiSym (ε*σ*U) p := by
  have hε0 : (ε:ZMod p)≠0 := by rcases hε with rfl | rfl <;> norm_num
  have hσ0 : (σ:ZMod p)≠0 := by rcases hσ with rfl | rfl <;> norm_num
  have hR0 := cast_ne p R hR
  have hU0 := cast_ne p U hU
  have hq0 := cast_ne p q hq
  have htwo : ¬(p:ℤ)∣2 := fun h => h6 (by simpa using dvd_mul_of_dvd_left h (3:ℤ))
  have h20 : (2:ZMod p)≠0 := by simpa using cast_ne p 2 htwo
  have hD0 : ((ε*R*U:ℤ):ZMod p)≠0 := by
    push_cast
    exact mul_ne_zero (mul_ne_zero hε0 hR0) hU0
  have hE0 : ((σ*2^α*R*q:ℤ):ZMod p)≠0 := by
    push_cast
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hσ0 (pow_ne_zero _ h20)) hR0) hq0
  have hD : ¬(p:ℤ)∣ε*R*U := fun hd => hD0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hd)
  have hs := AuxiliaryBadPrimeResidues318.selected_ratio p (ε*R*U) (σ*2^α*R*q) h6 hD T Y hB
  have hj := character_eq_of_square_ratio p (σ*2^α*R*q) (ε*R*U) hE0 hD0 hs
  simp only [jacobiSym.mul_left,jacobiSym.pow_left,h2,one_pow,mul_one] at hj
  have hR2 := jacobi_square_one p R hR0
  have hRn : jacobiSym R p≠0 := by intro hz; rw [hz] at hR2; norm_num at hR2
  have hc : jacobiSym σ p*jacobiSym q p=jacobiSym ε p*jacobiSym U p := by
    apply mul_left_cancel₀ hRn
    linear_combination hj
  have hσ2 := jacobi_square_one p σ hσ0
  rw [jacobiSym.mul_left,jacobiSym.mul_left]
  calc
    jacobiSym q p=(jacobiSym σ p)^2*jacobiSym q p := by rw [hσ2,one_mul]
    _=jacobiSym σ p*(jacobiSym ε p*jacobiSym U p) := by rw [pow_two,mul_assoc,hc]
    _=jacobiSym ε p*jacobiSym σ p*jacobiSym U p := by ring

/-- For an unselected coefficient prime, write t=-Aq. The actual B-side
and splitting6 imply J(q/p)=J(A/p), with units ensuring the modular square
is nonzero. Instantiation uses A=-sigma*2^alpha*P. -/
theorem unselected_identity (p : ℕ) [Fact p.Prime] (D A q : ℤ)
    (h6 : ¬(p:ℤ)∣6) (hD : ¬(p:ℤ)∣D)
    (hA : ¬(p:ℤ)∣A) (hq : ¬(p:ℤ)∣q) (hsix : jacobiSym 6 p=1)
    (T Y : ℚ_[p])
    (hB : (((p:ℤ)*D:ℤ):ℚ_[p])*T^2-6*Y^2=((-A*q:ℤ):ℚ_[p])) :
    jacobiSym q p=jacobiSym A p := by
  have hs := AuxiliaryBadPrimeResidues318.unselected_square p D (-A*q) h6 hD T Y hB
  have h6Aq : -6*(-A*q)=6*A*q := by ring
  rw [h6Aq] at hs
  have h60 := cast_ne p 6 h6
  have hA0 := cast_ne p A hA
  have hq0 := cast_ne p q hq
  have hj := jacobi_one_of_square p (6*A*q)
    (by simpa only [Int.cast_mul] using mul_ne_zero (mul_ne_zero h60 hA0) hq0) hs
  simp only [jacobiSym.mul_left,hsix,one_mul] at hj
  have hA2 := jacobi_square_one p A hA0
  calc
    jacobiSym q p=(jacobiSym A p)^2*jacobiSym q p := by rw [hA2,one_mul]
    _=jacobiSym A p*(jacobiSym A p*jacobiSym q p) := by ring
    _=jacobiSym A p := by rw [hj,mul_one]

end AuxiliaryLocalCharacters318
