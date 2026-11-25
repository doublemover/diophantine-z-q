module
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Basic
public import Mathlib.Tactic.Ring
public section
noncomputable section

namespace OriginalR47DyadicLiteralChi318

universe u v
variable {A : Type u} [CommRing A]

/-- Exact integral invariants of the long dyadic equation
`y² + (ρU)xy + y = x³`, with a₁=ρU and a₃=1. -/
abbrev c4 (ρ U : A) := (ρ * U)^4 - 24 * (ρ * U)
abbrev discr (ρ U : A) := (ρ * U)^3 - 27
abbrev numerator (ρ U : A) := U^3 * (U^3 - 6 * ρ)^3
abbrev denominator (ρ U : A) := 27 * (2 * ρ * U^3 - 27)

theorem invariant_reads (ρ U : A) (hr : ρ^2 = 2) :
    c4 ρ U = 4 * U * (U^3 - 6 * ρ) ∧
      discr ρ U = 2 * ρ * U^3 - 27 := by
  constructor
  · calc
      c4 ρ U = ρ^2 * ρ^2 * U^4 - 24 * (ρ * U) := by unfold c4; ring
      _ = _ := by rw [hr]; ring
  · calc
      discr ρ U = ρ^2 * ρ * U^3 - 27 := by unfold discr; ring
      _ = _ := by rw [hr]

section WholeField
variable {K : Type v} [CommRing K] [IsDomain A]

/-- This is the mixed-characteristic division *before* specialization,
using the actual injection of the chart into its selected generic
field. `hraw` is the real relation for the same j=1728χ map, not
an equality for an independently chosen residue parameter. -/
theorem exact_scaled (ι : A →+* K) (hi : Function.Injective ι) (ρ U χ : A)
    (hr : ρ^2 = 2) (h1728 : (1728 : A) ≠ 0)
    (hraw : ι (1728 * χ * discr ρ U) = ι ((c4 ρ U)^3)) :
    χ * denominator ρ U = numerator ρ U := by
  have hx : 1728 * χ * discr ρ U = (c4 ρ U)^3 := hi hraw
  obtain ⟨hc4,hΔ⟩ := invariant_reads ρ U hr
  apply mul_left_cancel₀ h1728
  calc
    1728 * (χ * denominator ρ U) =
        27 * (1728 * χ * discr ρ U) := by rw [hΔ]; unfold denominator; ring
    _ = 27 * (c4 ρ U)^3 := by rw [hx]
    _ = 1728 * numerator ρ U := by rw [hc4]; unfold numerator; ring

end WholeField

section ActualPrime
variable (z : PrimeSpectrum A)
local notation "p" => z.asIdeal
local notation "res" => Ideal.Quotient.mk p

/-- Full finite scaled χ reduces to U^12, not to zero as the unscaled
j always does in this open above the dyadic prime. No division by
1728 takes place in the residue ring. -/
theorem residue_scaled (ρ U χ : A)
    (h₂ : (2 : A) ∈ p) (hχ : χ * denominator ρ U = numerator ρ U) :
    res χ = res U ^ 12 := by
  have h2' : (2 : A ⧸ p) = 0 := by
    simpa only [map_ofNat] using ((Ideal.Quotient.eq_zero_iff_mem).mpr h₂ : res 2 = 0)
  have h27 : (27 : A ⧸ p) = 1 := by
    calc
      27 = 13 * (2 : A ⧸ p) + 1 := by ring
      _ = 1 := by rw [h2',mul_zero,zero_add]
  have h6 : (6 : A ⧸ p) = 0 := by
    calc
      6 = 3 * (2 : A ⧸ p) := by ring
      _ = 0 := by rw [h2',mul_zero]
  have hd : res (denominator ρ U) = 1 := by
    simp only [denominator,map_mul,map_sub,map_pow,map_ofNat,h2',h27,
      zero_mul,zero_sub,one_mul]
    -- In the geometric residue domain, -1=1 in characteristic two.
    apply neg_eq_iff_add_eq_zero.mpr
    calc
      (1 : A ⧸ p) + 1 = 2 := by ring
      _ = 0 := h2'
  have hn : res (numerator ρ U) = res U ^ 12 := by
    simp only [numerator,map_mul,map_sub,map_pow,map_ofNat,h6,zero_mul,sub_zero]
    ring
  have H := congrArg res hχ
  rwa [map_mul,hd,hn,mul_one] at H

/-- At the actual marked closed point, parity of the retained finite
coordinate distinguishes the *two-axis intersection* from the
unit-axis locus. In R26 the powers are 1,2; after the literal R29
primitive-4 normalization they are 4,8, with sign/unit factors.
The same statement handles their transported positive powers in R30.
Residue comparison to n is on the same chosen lift of the whole mark,
not a rule selecting an R8 branch by agreement of χ alone. -/
theorem actual_axes (ρ U χ x y a b : A) (n r s : ℕ)
    (h₂ : (2 : A) ∈ p)
    (hχ : χ * denominator ρ U = numerator ρ U) (hmark : res χ = (n : A ⧸ p))
    (hx : r ≠ 0) (hy : s ≠ 0) (ha : a ∉ p) (hb : b ∉ p)
    (hcross : x * y ∈ p) (hU : res U = res a * res x^r + res b * res y^s) :
    (n : A) ∈ p ↔ x ∈ p ∧ y ∈ p := by
  letI : p.IsPrime := z.isPrime
  have hU0 : res U = 0 ↔ res x = 0 ∧ res y = 0 := by
    have hxy : res x * res y = 0 := by
      rw [← map_mul]
      exact (Ideal.Quotient.eq_zero_iff_mem).mpr hcross
    have ha' : res a ≠ 0 := fun h => ha ((Ideal.Quotient.eq_zero_iff_mem).mp h)
    have hb' : res b ≠ 0 := fun h => hb ((Ideal.Quotient.eq_zero_iff_mem).mp h)
    constructor
    · intro h
      rw [hU] at h
      rcases mul_eq_zero.mp hxy with H | H
      · rw [H,zero_pow hx,mul_zero,zero_add] at h
        exact ⟨H,(pow_eq_zero_iff hy).mp ((mul_eq_zero.mp h).resolve_left hb')⟩
      · rw [H,zero_pow hy,mul_zero,add_zero] at h
        exact ⟨(pow_eq_zero_iff hx).mp ((mul_eq_zero.mp h).resolve_left ha'),H⟩
    · rintro ⟨hx0,hy0⟩
      rw [hU,hx0,hy0,zero_pow hx,zero_pow hy,mul_zero,mul_zero,add_zero]
  have hh : (n : A ⧸ p) = res U ^ 12 := hmark.symm.trans (residue_scaled z ρ U χ h₂ hχ)
  calc
    (n : A) ∈ p ↔ (n : A ⧸ p) = 0 := by rw [← map_natCast res,Ideal.Quotient.eq_zero_iff_mem]
    _ ↔ res U = 0 := by rw [hh,pow_eq_zero_iff (by decide : (12:ℕ) ≠ 0)]
    _ ↔ x ∈ p ∧ y ∈ p := by
      simp only [hU0,Ideal.Quotient.eq_zero_iff_mem]

section Exact
variable {K : Type v} [CommRing K] [IsDomain A]

/-- Characteristic-two read on the literal same-function-field model.
The entire point has already been selected over the R8 section; the
conclusion is not used to select it. In particular a third point with
the same residue χ is not substituted for the fixed mark. -/
theorem actual_even_axes (ι : A →+* K) (hi : Function.Injective ι)
    (ρ U χ x y a b : A) (n r s : ℕ) (hrho : ρ^2 = 2)
    (h1728 : (1728 : A) ≠ 0) (hraw : ι (1728 * χ * discr ρ U) = ι ((c4 ρ U)^3))
    (h₂ : (2 : A) ∈ p) (hmark : res χ = (n : A ⧸ p))
    (hx : r ≠ 0) (hy : s ≠ 0) (ha : a ∉ p) (hb : b ∉ p)
    (hcross : x * y ∈ p) (hU : res U = res a * res x^r + res b * res y^s) :
    Even n ↔ x ∈ p ∧ y ∈ p := by
  letI : p.IsPrime := z.isPrime
  have h2' : (2 : A ⧸ p) = 0 := by
    simpa only [map_ofNat] using ((Ideal.Quotient.eq_zero_iff_mem).mpr h₂ : res 2 = 0)
  letI : CharP (A ⧸ p) 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).mpr h2'
  have hχ := exact_scaled ι hi ρ U χ hrho h1728 hraw
  refine (?_ : Even n ↔ (n : A) ∈ p).trans
    (actual_axes z ρ U χ x y a b n r s h₂ hχ hmark hx hy ha hb hcross hU)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero_iff (A ⧸ p) 2 n, even_iff_two_dvd]

end Exact

end ActualPrime
end OriginalR47DyadicLiteralChi318

#print axioms OriginalR47DyadicLiteralChi318.exact_scaled
#print axioms OriginalR47DyadicLiteralChi318.residue_scaled
#print axioms OriginalR47DyadicLiteralChi318.actual_axes

#print axioms OriginalR47DyadicLiteralChi318.actual_even_axes
