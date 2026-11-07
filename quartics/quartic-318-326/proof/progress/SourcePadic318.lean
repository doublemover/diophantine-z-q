module
public import ConcretePadic318
public import SourceContact318
public section
namespace SourcePadic318
open ConcreteG8Domain ConcretePadic318 SourceContact318
open scoped QuadraticAlgebra

/-- Both discriminant factors are units at every place above a prime away
from 2, 3 and 7; no independent unit premise is needed for either orientation. -/
theorem discriminant_units (v : AddValuation K (WithTop ℤ))
    (h2 : v (2:K)=0) (h3 : v (3:K)=0) (h7 : v (7:K)=0) :
    v (pair 11 6)=0 ∧ v (pair 11 (-6))=0 := by
  have hi0 : i≠0 := by intro h; have hh := congrArg QuadraticAlgebra.im h; norm_num [i,pair] at hh
  obtain ⟨a,ha⟩ := WithTop.ne_top_iff_exists.mp ((v.ne_top_iff).mpr hi0)
  have hsq := congrArg v i_square
  rw [v.map_pow,←ha,h2] at hsq
  have hai : a=0 := by
    have he : 2*a=0 := by exact_mod_cast hsq
    omega
  have hi : v i=0 := by simpa [hai] using ha.symm
  have hplus : pair 11 6=(3+i)^2 := by ext <;> norm_num [i,pair,pow_two] <;> ring
  have hminus : pair 11 (-6)=(3-i)^2 := by ext <;> norm_num [i,pair,pow_two] <;> ring
  have hpos : 0≤v (pair 11 6) := by
    rw [hplus,v.map_pow]
    exact nsmul_nonneg (v.map_le_add (by rw [h3]) (by rw [hi])) _
  have hneg : 0≤v (pair 11 (-6)) := by
    rw [hminus,v.map_pow]
    exact nsmul_nonneg (v.map_le_sub (by rw [h3]) (by rw [hi])) _
  have hnorm : pair 11 6*pair 11 (-6)=(7:K)^2 := by ext <;> norm_num [pair,pow_two]
  have hh := congrArg v hnorm
  rw [v.map_mul,v.map_pow,h7] at hh
  simp only [nsmul_zero] at hh
  have hle1 : v (pair 11 6)≤0 := by
    calc
      v (pair 11 6)=v (pair 11 6)+0 := by simp
      _≤v (pair 11 6)+v (pair 11 (-6)) := add_le_add (le_refl _) hneg
      _=0 := hh
  have hle2 : v (pair 11 (-6))≤0 := by
    calc
      v (pair 11 (-6))=0+v (pair 11 (-6)) := by simp
      _≤v (pair 11 6)+v (pair 11 (-6)) := add_le_add hpos (le_refl _)
      _=0 := hh
  exact ⟨le_antisymm hle1 hpos,le_antisymm hle2 hneg⟩

variable (p : ℕ) [Fact p.Prime]

theorem place_nat_unit (rho : ℚ_[p]) (hr : rho^2=2) (n : ℕ) (hn : ¬p∣n) :
    place p rho hr (n:K)=0 := by
  have hid : (n:K)=pair (n:ℚ) 0 := by ext <;> simp [pair]
  rw [hid,place_rational,rational_nat_unit p n hn]

theorem conjugate_place (rho : ℚ_[p]) (hr : rho^2=2) (z : K) :
    place p rho hr (conj z)=place p (-rho) (negative_root p rho hr) z := by
  obtain ⟨a,b⟩ := z
  change place p rho hr (pair a (-b))=place p (-rho) (negative_root p rho hr) (pair a b)
  simp only [place_pair,Rat.cast_neg,neg_mul,mul_neg]

@[simp] theorem rational_place (rho : ℚ_[p]) (hr : rho^2=2) (q : ℚ) :
    rational (place p rho hr) q=rationalPlace p q := place_rational p rho hr q

open CircuitReplay Raw318FinalReplay RawWeights318

/-- The full literal detector at an actual split p-adic place. -/
theorem contact0_at_padic (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (rho : ℚ_[p]) (hr : rho^2=2) (a f : ℤ)
    (hA : rationalPlace p (A0 S w)=a) (hF : rationalPlace p (F0 S w)=f)
    (hd : rationalPlace p (delta0 S w)=0) (hf : Odd f)
    (hp2 : ¬p∣2) (hp3 : ¬p∣3) (hp7 : ¬p∣7) (hp17 : ¬p∣17) :
    0<f-5*a ∧ ((∀x∈inputs0 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1) ∨
      (∀x∈inputs0 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1)) := by
  have h2 := place_nat_unit p rho hr 2 hp2
  have h3 := place_nat_unit p rho hr 3 hp3
  have h7 := place_nat_unit p rho hr 7 hp7
  have h17 := place_nat_unit p rho hr 17 hp17
  obtain ⟨hD,hDc⟩ := discriminant_units (place p rho hr) h2 h3 h7
  have hh := contact0_extract S w source (place p rho hr) a f
    (by simpa only [rational_place] using hA) (by simpa only [rational_place] using hF) (by simpa only [rational_place] using hd) hf hD hDc h2 h3 h17
  simpa only [conjugate_place] using hh

/-- The full literal detector at an actual split p-adic place. -/
theorem contact1_at_padic (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (rho : ℚ_[p]) (hr : rho^2=2) (a f : ℤ)
    (hA : rationalPlace p (A1 S w)=a) (hF : rationalPlace p (F1 S w)=f)
    (hd : rationalPlace p (delta1 S w)=0) (hf : Odd f)
    (hp2 : ¬p∣2) (hp3 : ¬p∣3) (hp7 : ¬p∣7) (hp17 : ¬p∣17) :
    0<f-5*a ∧ ((∀x∈inputs1 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1) ∨
      (∀x∈inputs1 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1)) := by
  have h2 := place_nat_unit p rho hr 2 hp2
  have h3 := place_nat_unit p rho hr 3 hp3
  have h7 := place_nat_unit p rho hr 7 hp7
  have h17 := place_nat_unit p rho hr 17 hp17
  obtain ⟨hD,hDc⟩ := discriminant_units (place p rho hr) h2 h3 h7
  have hh := contact1_extract S w source (place p rho hr) a f
    (by simpa only [rational_place] using hA) (by simpa only [rational_place] using hF) (by simpa only [rational_place] using hd) hf hD hDc h2 h3 h17
  simpa only [conjugate_place] using hh

/-- The full literal detector at an actual split p-adic place. -/
theorem contact2_at_padic (S : ℚ) (w : Assignment) (source : Constraints (stage0 S) w)
    (rho : ℚ_[p]) (hr : rho^2=2) (a f : ℤ)
    (hA : rationalPlace p (A2 S w)=a) (hF : rationalPlace p (F2 S w)=f)
    (hd : rationalPlace p (delta2 S w)=0) (hf : Odd f)
    (hp2 : ¬p∣2) (hp3 : ¬p∣3) (hp7 : ¬p∣7) (hp17 : ¬p∣17) :
    0<f-5*a ∧ ((∀x∈inputs2 S w,(2*x.2.2:ℤ)≤place p rho hr x.2.1) ∨
      (∀x∈inputs2 S w,(2*x.2.2:ℤ)≤place p (-rho) (negative_root p rho hr) x.2.1)) := by
  have h2 := place_nat_unit p rho hr 2 hp2
  have h3 := place_nat_unit p rho hr 3 hp3
  have h7 := place_nat_unit p rho hr 7 hp7
  have h17 := place_nat_unit p rho hr 17 hp17
  obtain ⟨hD,hDc⟩ := discriminant_units (place p rho hr) h2 h3 h7
  have hh := contact2_extract S w source (place p rho hr) a f
    (by simpa only [rational_place] using hA) (by simpa only [rational_place] using hF) (by simpa only [rational_place] using hd) hf hD hDc h2 h3 h17
  simpa only [conjugate_place] using hh

end SourcePadic318
