module
public import ThreeGroupSteps318
public section
namespace GeneratorMultiplesThree318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine ThreeGroupSteps318
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Ternary induction around Q=2P proves the exact local index valuation. -/
theorem positive_multiple (n : ℕ) (hn : 0<n) :
    Depth (n • Q) (-4-4*(padicValNat 3 n:ℤ)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n=1
    · subst n
      simpa using base_depth
    have hn2 : 2≤n := by omega
    by_cases hdiv : 3∣n
    · let k := n/3
      have hnk : n=3*k := by obtain ⟨j,hj⟩ := hdiv; dsimp [k]; omega
      have hk : 0<k := by omega
      have hkn : k<n := by omega
      have hR := ih k hkn hk
      have hT := triple_depth (k • Q) _ hR (by omega)
      have hvn : padicValNat 3 n=1+padicValNat 3 k := by
        rw [hnk,padicValNat.mul (by norm_num) (by omega)]
        congr 1
        exact padicValNat.self (by norm_num)
      rw [hvn,hnk,Nat.mul_comm 3 k,mul_nsmul]
      convert hT using 1
      push_cast
      ring
    · have hvn : padicValNat 3 n=0 := padicValNat.eq_zero_of_not_dvd hdiv
      have hmod : n%3=1 ∨ n%3=2 := by
        have hzero : n%3≠0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hdiv
        omega
      rcases hmod with hm | hm
      · let k := n/3
        have hnk : n=3*k+1 := by dsimp [k]; omega
        have hk : 0<k := by omega
        have hkn : k<n := by omega
        have hR := ih k hkn hk
        have hT := triple_depth (k • Q) _ hR (by omega)
        have hA := add_depth _ Q _ (-4) hT base_depth (by omega) (by norm_num)
        rw [hvn,hnk,add_nsmul,Nat.mul_comm 3 k,mul_nsmul,one_nsmul]
        simpa only [hvn,Nat.cast_zero,mul_zero,sub_zero] using hA
      · let k := (n+1)/3
        have hnk : n+1=3*k := by dsimp [k]; omega
        have hk : 0<k := by omega
        have hkn : k<n := by omega
        have hR := ih k hkn hk
        have hT := triple_depth (k • Q) _ hR (by omega)
        have hA := add_depth _ (-Q) _ (-4) hT (neg_depth Q (-4) base_depth) (by omega) (by norm_num)
        have heq : n • Q=(3:ℕ) • (k • Q)+ -Q := by
          calc
            n • Q=(n+1) • Q-Q := by rw [add_nsmul,one_nsmul,add_sub_cancel_right]
            _ = (3:ℕ) • (k • Q)+ -Q := by
              rw [hnk,Nat.mul_comm 3 k,mul_nsmul]
              rfl
        rw [heq]
        simpa only [hvn,Nat.cast_zero,mul_zero,sub_zero] using hA

theorem integer_multiple (n : ℤ) (hn : n≠0) :
    Depth (n • Q) (-4-4*(padicValInt 3 n:ℤ)) := by
  have hnat : 0<n.natAbs := Int.natAbs_pos.mpr hn
  have hD := positive_multiple n.natAbs hnat
  rcases le_total 0 n with hpos | hneg
  · have he : (n.natAbs:ℤ)=n := by rw [Int.natCast_natAbs,abs_of_nonneg hpos]
    rw [←he,natCast_zsmul]
    exact hD
  · have he : n= -(n.natAbs:ℤ) := by rw [Int.natCast_natAbs,abs_of_nonpos hneg,neg_neg]
    rw [he,neg_zsmul,natCast_zsmul]
    simpa only [padicValInt,Int.natAbs_neg,Int.natAbs_natCast] using neg_depth _ _ hD

/-- Every nonzero even index on P has the required exact 3-adic norm
valuation. Formal-group series and a reduction homomorphism are not assumed. -/
theorem even_multiple (c : ℤ) (hc : c≠0) (heven : Even c) :
    Depth (c • P) (-4-4*(padicValInt 3 c:ℤ)) := by
  obtain ⟨m,hm⟩ := heven
  have hcm : c=2*m := by omega
  have hm0 : m≠0 := by intro h; rw [hcm,h] at hc; simp at hc
  have hv : padicValInt 3 c=padicValInt 3 m := by
    have hq : padicValRat 3 (c:ℚ)=padicValRat 3 (m:ℚ) := by
      rw [hcm,Int.cast_mul,padicValRat.mul (by norm_num) (by exact_mod_cast hm0)]
      have hh : padicValRat 3 (2:ℚ)=0 := by
        simpa using AnchorNorm318.rational_unit_value 3 2 1 (by norm_num) (by norm_num)
      norm_num only [Int.cast_ofNat] at *
      rw [hh,zero_add]
    simpa only [padicValRat.of_int,Nat.cast_inj] using hq
  have hD := integer_multiple m hm0
  have hpoint : c • P=m • Q := by
    simp only [hcm,mul_zsmul,Q,two_zsmul,zsmul_add]
  rw [hpoint,hv]
  exact hD

theorem identified_even_multiple_norm (c : ℤ) (hc : c≠0) (heven : Even c)
    (x y : K) (h : E.Nonsingular x y) (hpt : c • P=Point.some x y h) :
    padicValRat 3 (AnchorNorm318.norm x)= -4-4*(padicValInt 3 c:ℤ) := by
  obtain ⟨x',y',h',hpt',hv⟩ := even_multiple c hc heven
  have he : Point.some x' y' h'=Point.some x y h := hpt'.symm.trans hpt
  cases he
  have hx : x≠0 := (InertThree318.place.ne_top_iff).mp (by rw [hv]; exact WithTop.coe_ne_top)
  rw [InertThree318.place_norm _ hx] at hv
  exact_mod_cast hv

end GeneratorMultiplesThree318
