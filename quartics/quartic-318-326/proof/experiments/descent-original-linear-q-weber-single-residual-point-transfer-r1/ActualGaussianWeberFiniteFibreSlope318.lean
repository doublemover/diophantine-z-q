module
public import ActualGaussianWeberHenselianPointMap318
public section
noncomputable section

namespace ActualGaussianWeberFiniteFibreSlope318

open IsLocalRing ActualGaussianWeberHenselianPointMap318

variable {F : Type*} [Field F] (V : ValuationSubring F)

theorem unit_over_small_is_nonintegral (n d : V)
    (hn : residue V n ≠ 0) (hd : residue V d = 0)
    (hdF : V.subtype d ≠ 0) :
    V.subtype n / V.subtype d ∉ V := by
  intro hi
  let q : V := ⟨V.subtype n / V.subtype d,hi⟩
  have hq : q*d=n := by
    apply V.subtype_injective
    rw [map_mul]
    change (V.subtype n / V.subtype d)*V.subtype d=V.subtype n
    exact div_mul_cancel₀ _ hdF
  apply hn
  rw [←hq,map_mul,hd,mul_zero]

theorem simple_zero_branch {K : Type*} [Field K] (h2 : (2:K) ≠ 0)
    {x : K} (hx : x^3-x=0) : (3:K)*x^2-1 ≠ 0 := by
  have hX : x*(x^2-1)=0 := by linear_combination hx
  rcases mul_eq_zero.mp hX with h | h
  · simp [h]
  · have hR := sub_eq_zero.mp h
    rw [hR]
    convert h2 using 1 <;> ring

/-- The two finite original points have the same residue, different
generic abscissae. On subtracting Q, the true secant slope is a pole.
At residue y=0 use the factored Weber equation before dividing. -/
theorem distinct_x_secant_pole (h2 : (2:ResidueField V) ≠ 0)
    (a b c d : V) (he₁ : b^2=a^3-a) (he₂ : d^2=c^3-c)
    (hx : residue V a=residue V c) (hy : residue V b=residue V d)
    (hAC : V.subtype a ≠ V.subtype c) :
    (V.subtype b+V.subtype d)/(V.subtype a-V.subtype c) ∉ V := by
  by_cases hY : residue V b=0
  · let n : V := a^2+a*c+c^2-1
    have Hx : residue V a^3-residue V a=0 := by
      have h := equation_in_residue V a b he₁
      simpa only [hY,zero_pow (by decide : (2:ℕ) ≠ 0)] using h.symm
    have hN : residue V n ≠ 0 := by
      rw [show residue V n=(3:ResidueField V)*(residue V a)^2-1 by
        simp only [n,map_sub,map_add,map_mul,map_pow,map_one,←hx]; ring]
      exact simple_zero_branch h2 Hx
    have hb : residue V (b-d)=0 := by rw [map_sub,hy,sub_self]
    have hcross : (b+d)*(b-d)=(a-c)*n := by
      change (b+d)*(b-d)=(a-c)*(a^2+a*c+c^2-1)
      linear_combination he₁-he₂
    have hF := congrArg V.subtype hcross
    simp only [map_mul,map_sub,map_add] at hF
    have hn0 : V.subtype n ≠ 0 := by
      intro H
      exact hN (by rw [V.subtype_injective (H.trans (map_zero _).symm),map_zero])
    have hD : V.subtype b - V.subtype d ≠ 0 := by
      intro H
      apply mul_ne_zero (sub_ne_zero.mpr hAC) hn0
      rw [←hF,H,mul_zero]
    have hs : (V.subtype b+V.subtype d)/(V.subtype a-V.subtype c) =
        V.subtype n/(V.subtype b-V.subtype d) := by
      apply (div_eq_div_iff (sub_ne_zero.mpr hAC) hD).mpr
      simpa only [mul_comm (V.subtype n)] using hF
    rw [hs,←map_sub]
    exact unit_over_small_is_nonintegral V n (b-d) hN hb (by simpa only [map_sub] using hD)
  · have hN : residue V (b+d) ≠ 0 := by
      rw [map_add,←hy,←two_mul]
      exact mul_ne_zero h2 hY
    have hd : residue V (a-c)=0 := by rw [map_sub,hx,sub_self]
    rw [←map_add,←map_sub]
    exact unit_over_small_is_nonintegral V (b+d) (a-c) hN hd
      (by simpa only [map_sub] using sub_ne_zero.mpr hAC)

/-- The coincident successful tangent branch at a residual 2-torsion
point has the same pole, using (3a²−1)/(2b). -/
theorem residue_two_torsion_tangent_pole (h2 : (2:ResidueField V) ≠ 0)
    (a b : V) (he : b^2=a^3-a) (hY : residue V b=0)
    (hDF : (2:F)*V.subtype b ≠ 0) :
    ((3:F)*(V.subtype a)^2-1)/((2:F)*V.subtype b) ∉ V := by
  have Hx : residue V a^3-residue V a=0 := by
    have h := equation_in_residue V a b he
    simpa only [hY,zero_pow (by decide : (2:ℕ) ≠ 0)] using h.symm
  have hn : residue V ((3:V)*a^2-1) ≠ 0 := by
    simpa only [map_sub,map_mul,map_pow,map_one,map_ofNat] using simple_zero_branch h2 Hx
  have hd : residue V ((2:V)*b)=0 := by rw [map_mul,hY,mul_zero]
  have hDF' : V.subtype ((2:V)*b) ≠ 0 := by simpa only [map_mul,map_ofNat] using hDF
  simpa only [map_sub,map_mul,map_pow,map_one,map_ofNat] using
    unit_over_small_is_nonintegral V ((3:V)*a^2-1) ((2:V)*b) hn hd hDF'

theorem subtraction_abscissa_pole {a b ell : F} (ha : a∈V) (hb : b∈V) (h : ell ∉ V) :
    ell^2-a-b ∉ V := by
  intro H
  have E : ell^2-a-b+a+b=ell^2 := by ring
  exact h (integral_square V (E ▸ add_mem (add_mem H ha) hb))

end ActualGaussianWeberFiniteFibreSlope318
