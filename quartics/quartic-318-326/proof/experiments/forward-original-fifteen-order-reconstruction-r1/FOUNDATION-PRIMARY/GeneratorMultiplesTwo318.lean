module
public import ValuationAddition318
public section
namespace GeneratorMultiplesTwo318
open ConcreteG8Domain LocalGenerator318 WeierstrassCurve.Affine
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- Exact 2-adic valuation of every positive multiple of the actual generator.
Binary induction uses actual elliptic addition and doubling, not an assumed
formal logarithm or analytic isometry. -/
theorem positive_multiple (n : ℕ) (hn : 0<n) :
    ∃ (x y : K) (h : E.Nonsingular x y), n • P=Point.some x y h ∧
      RamifiedTwo318.place x=(-6-4*(padicValNat 2 n:ℤ):ℤ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases h1 : n=1
    · subst n
      refine ⟨xP,yP,nonsingularP,by simp [P],?_⟩
      simpa using RamifiedTwo318.generator_x_value
    let k := n/2
    have hn2 : 2≤n := by omega
    have hk : 0<k := by dsimp [k]; omega
    have hkn : k<n := by dsimp [k]; omega
    obtain ⟨x,y,h,hpoint,hval⟩ := ih k hkn hk
    have ha : -6-4*(padicValNat 2 k:ℤ)<0 := by omega
    obtain ⟨hd,hdouble,hvd⟩ := ValuationDuplication318.actual_two_doubling x y h _ hval ha
    rcases Nat.even_or_odd n with heven | hodd
    · have hnk : n=2*k := by
        obtain ⟨j,hj⟩ := heven
        dsimp [k]
        omega
      have hvn : padicValNat 2 n=1+padicValNat 2 k := by
        rw [hnk,padicValNat.mul (by norm_num) (by omega)]
        congr 1
        exact padicValNat.self (by norm_num)
      refine ⟨_,_,hd,?_,?_⟩
      · rw [hnk,Nat.mul_comm 2 k,mul_nsmul,two_nsmul,hpoint]
        exact hdouble
      · rw [hvd,hvn]
        norm_cast
        omega
    · have hnk : n=2*k+1 := by
        obtain ⟨j,hj⟩ := hodd
        dsimp [k]
        omega
      have hvn : padicValNat 2 n=0 := padicValNat.eq_zero_of_not_dvd (by
        intro hh
        obtain ⟨j,hj⟩ := hh
        omega)
      have ha' : -6-4*(padicValNat 2 k:ℤ)-4< -6 := by omega
      obtain ⟨hs,hsum,hvs⟩ := ValuationAddition318.actual_two_unequal_add
        _ _ xP yP hd nonsingularP _ (-6) hvd RamifiedTwo318.generator_x_value ha' (by norm_num)
      refine ⟨_,_,hs,?_,?_⟩
      · rw [hnk,add_nsmul,Nat.mul_comm 2 k,mul_nsmul,two_nsmul,one_nsmul,hpoint,hdouble]
        exact hsum
      · simpa [hvn] using hvs

/-- Every nonzero integer multiple has finite nonzero abscissa with the exact
rational norm valuation required by the compressed parity anchor. -/
theorem integer_multiple (n : ℤ) (hn : n≠0) :
    ∃ (x y : K) (h : E.Nonsingular x y), n • P=Point.some x y h ∧
      RamifiedTwo318.place x=(-6-4*(padicValInt 2 n:ℤ):ℤ) := by
  have hnat : 0<n.natAbs := Int.natAbs_pos.mpr hn
  obtain ⟨x,y,h,hpt,hv⟩ := positive_multiple n.natAbs hnat
  rcases le_total 0 n with hpos | hneg
  · have he : (n.natAbs:ℤ)=n := by rw [Int.natCast_natAbs,abs_of_nonneg hpos]
    refine ⟨x,y,h,?_,hv⟩
    rw [←he,natCast_zsmul]
    exact hpt
  · have he : n= -(n.natAbs:ℤ) := by
      rw [Int.natCast_natAbs,abs_of_nonpos hneg,neg_neg]
    refine ⟨x,E.negY x y,(nonsingular_neg x y).mpr h,?_,hv⟩
    rw [he,neg_zsmul,natCast_zsmul,hpt]
    rfl

theorem norm_integer_multiple (n : ℤ) (hn : n≠0) :
    ∃ (x y : K) (h : E.Nonsingular x y), n • P=Point.some x y h ∧
      AnchorNorm318.norm x≠0 ∧
      padicValRat 2 (AnchorNorm318.norm x)= -6-4*(padicValInt 2 n:ℤ) := by
  obtain ⟨x,y,h,hpt,hv⟩ := integer_multiple n hn
  have hx : x≠0 := (RamifiedTwo318.place.ne_top_iff).mp (by rw [hv]; exact WithTop.coe_ne_top)
  refine ⟨x,y,h,hpt,AnchorNorm318.norm_ne_zero hx,?_⟩
  rw [RamifiedTwo318.place_norm x hx] at hv
  exact_mod_cast hv

/-- No nonzero integer kills P; this proves infinite order without importing
the still separate global Mordell–Weil generator/rank theorem. -/
theorem generator_infinite_order (n : ℤ) (hn : n≠0) : n • P≠0 := by
  obtain ⟨x,y,h,hpt,_⟩ := integer_multiple n hn
  rw [hpt]
  exact Point.some_ne_zero _

/-- Reusable coordinate form: the supplied point is an actual multiple in
Mathlib's elliptic group, so no valuation formula is an input hypothesis. -/
theorem identified_multiple_norm (n : ℤ) (hn : n≠0) (x y : K)
    (h : E.Nonsingular x y) (hpt : n • P=Point.some x y h) :
    padicValRat 2 (AnchorNorm318.norm x)= -6-4*(padicValInt 2 n:ℤ) := by
  obtain ⟨x',y',h',hpt',_,hv⟩ := norm_integer_multiple n hn
  have he : Point.some x' y' h'=Point.some x y h := hpt'.symm.trans hpt
  cases he
  exact hv

end GeneratorMultiplesTwo318
