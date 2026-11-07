module
public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public section
namespace SemilocalAnchor318
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def anchorForm (u v w t d : ℤ) : ℤ := u^2+6*v^2-2*w^2-3*t^2+2*d^2

private theorem square_mod16 (x : ℤ) :
    (x^2%16=0 ∧ 2∣x) ∨ (x^2%16=4 ∧ 2∣x) ∨
      (x^2%16=1 ∧ ¬2∣x) ∨ (x^2%16=9 ∧ ¬2∣x) := by
  have hb : 0≤x%16 ∧ x%16<16 := ⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
  have heq : x^2%16=(x%16)^2%16 := by simp [pow_two,Int.mul_emod]
  rw [heq]
  have hdiv : 2∣x ↔ x%2=0 := Int.dvd_iff_emod_eq_zero
  rw [hdiv]
  obtain ⟨hb0,hb1⟩ := hb
  interval_cases h : x%16 <;> norm_num <;> omega

private theorem square_mod9 (x : ℤ) :
    (x^2%9=0 ∧ 3∣x) ∨ x^2%9=1 ∨ x^2%9=4 ∨ x^2%9=7 := by
  have hb : 0≤x%9 ∧ x%9<9 := ⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
  have heq : x^2%9=(x%9)^2%9 := by simp [pow_two,Int.mul_emod]
  rw [heq]
  have hdiv : 3∣x ↔ x%3=0 := Int.dvd_iff_emod_eq_zero
  rw [hdiv]
  obtain ⟨hb0,hb1⟩ := hb
  interval_cases h : x%9 <;> norm_num <;> omega

/-- The 2-adic division-quaternion obstruction, proved by exact residues. -/
theorem even_of_norm_mod16 (u v w t : ℤ)
    (h : (u^2+6*v^2-2*w^2-3*t^2)%16=0) :
    2∣u ∧ 2∣v ∧ 2∣w ∧ 2∣t := by
  have hu := square_mod16 u
  have hv := square_mod16 v
  have hw := square_mod16 w
  have ht := square_mod16 t
  simp only [Int.add_emod,Int.sub_emod,Int.mul_emod,Int.emod_emod] at h
  rcases hu with ⟨hu,hu2⟩|⟨hu,hu2⟩|⟨hu,hu2⟩|⟨hu,hu2⟩ <;>
    rcases hv with ⟨hv,hv2⟩|⟨hv,hv2⟩|⟨hv,hv2⟩|⟨hv,hv2⟩ <;>
    rcases hw with ⟨hw,hw2⟩|⟨hw,hw2⟩|⟨hw,hw2⟩|⟨hw,hw2⟩ <;>
    rcases ht with ⟨ht,ht2⟩|⟨ht,ht2⟩|⟨ht,ht2⟩|⟨ht,ht2⟩ <;>
    simp_all

/-- The analogous 3-adic obstruction needs only modulus nine. -/
theorem triple_of_norm_mod9 (u v w t : ℤ)
    (h : (u^2+6*v^2-2*w^2-3*t^2)%9=0) :
    3∣u ∧ 3∣v ∧ 3∣w ∧ 3∣t := by
  have hu := square_mod9 u
  have hv := square_mod9 v
  have hw := square_mod9 w
  have ht := square_mod9 t
  simp only [Int.add_emod,Int.sub_emod,Int.mul_emod,Int.emod_emod] at h
  rcases hu with ⟨hu,hu3⟩|hu|hu|hu <;>
    rcases hv with ⟨hv,hv3⟩|hv|hv|hv <;>
    rcases hw with ⟨hw,hw3⟩|hw|hw|hw <;>
    rcases ht with ⟨ht,ht3⟩|ht|ht|ht <;>
    simp_all

private theorem square_mod8 (x : ℤ) :
    (x^2%8=0 ∧ 2∣x) ∨ (x^2%8=4 ∧ 2∣x) ∨ (x^2%8=1 ∧ ¬2∣x) := by
  have hb : 0≤x%8 ∧ x%8<8 := ⟨Int.emod_nonneg _ (by norm_num),Int.emod_lt_of_pos _ (by norm_num)⟩
  have heq : x^2%8=(x%8)^2%8 := by simp [pow_two,Int.mul_emod]
  rw [heq]
  have hdiv : 2∣x ↔ x%2=0 := Int.dvd_iff_emod_eq_zero
  rw [hdiv]
  obtain ⟨hb0,hb1⟩ := hb
  interval_cases h : x%8 <;> norm_num <;> omega

theorem even_t_of_norm_mod8 (u v w t : ℤ)
    (h : (u^2+6*v^2-2*w^2-3*t^2)%8=0) : 2∣t := by
  have hu := square_mod8 u
  have hv := square_mod8 v
  have hw := square_mod8 w
  have ht := square_mod8 t
  simp only [Int.add_emod,Int.sub_emod,Int.mul_emod,Int.emod_emod] at h
  rcases hu with ⟨hu,hu2⟩|⟨hu,hu2⟩|⟨hu,hu2⟩ <;>
    rcases hv with ⟨hv,hv2⟩|⟨hv,hv2⟩|⟨hv,hv2⟩ <;>
    rcases hw with ⟨hw,hw2⟩|⟨hw,hw2⟩|⟨hw,hw2⟩ <;>
    rcases ht with ⟨ht,ht2⟩|⟨ht,ht2⟩|⟨ht,ht2⟩ <;>
    simp_all

theorem even_t_of_even_den (u v w t d : ℤ)
    (h : anchorForm u v w t d=0) (hd : 2∣d) : 2∣t := by
  obtain ⟨j,rfl⟩ := hd
  apply even_t_of_norm_mod8 u v w t
  have heq : u^2+6*v^2-2*w^2-3*t^2= -8*j^2 := by
    unfold anchorForm at h
    linear_combination h
  rw [heq,Int.mul_emod]
  norm_num

theorem even_all_of_four_den (u v w t d : ℤ)
    (h : anchorForm u v w t d=0) (hd : 4∣d) :
    2∣u ∧ 2∣v ∧ 2∣w ∧ 2∣t := by
  obtain ⟨j,rfl⟩ := hd
  apply even_of_norm_mod16 u v w t
  have heq : u^2+6*v^2-2*w^2-3*t^2= -32*j^2 := by
    unfold anchorForm at h
    linear_combination h
  rw [heq,Int.mul_emod]
  norm_num

theorem triple_all_of_triple_den (u v w t d : ℤ)
    (h : anchorForm u v w t d=0) (hd : 3∣d) :
    3∣u ∧ 3∣v ∧ 3∣w ∧ 3∣t := by
  obtain ⟨j,rfl⟩ := hd
  apply triple_of_norm_mod9 u v w t
  have heq : u^2+6*v^2-2*w^2-3*t^2= -18*j^2 := by
    unfold anchorForm at h
    linear_combination h
  rw [heq,Int.mul_emod]
  norm_num

theorem anchorForm_scale (p u v w t d : ℤ) :
    anchorForm (p*u) (p*v) (p*w) (p*t) (p*d)=p^2*anchorForm u v w t d := by
  unfold anchorForm
  ring

theorem two_power_transfer (k : ℕ) (u v w t d : ℤ)
    (h : anchorForm u v w t d=0) (hd : (2:ℤ)^k∣d) : (2:ℤ)^k∣t := by
  induction k generalizing u v w t d with
  | zero => simp
  | succ k ih =>
    cases k with
    | zero => simpa using even_t_of_even_den u v w t d h (by simpa using hd)
    | succ k =>
      have hd4 : (4:ℤ)∣d :=
        dvd_trans (by
          change (2:ℤ)^2∣2^(k+1+1)
          exact pow_dvd_pow 2 (by omega)) hd
      obtain ⟨hu,hv,hw,ht⟩ := even_all_of_four_den u v w t d h hd4
      have hd2 : (2:ℤ)∣d := dvd_trans (by norm_num : (2:ℤ)∣4) hd4
      obtain ⟨u,rfl⟩ := hu
      obtain ⟨v,rfl⟩ := hv
      obtain ⟨w,rfl⟩ := hw
      obtain ⟨t,rfl⟩ := ht
      obtain ⟨d,rfl⟩ := hd2
      have hred : anchorForm u v w t d=0 := by
        rw [anchorForm_scale] at h
        norm_num at h
        exact h
      have hd' : (2:ℤ)^(k+1)∣d := by
        rw [pow_succ'] at hd
        exact (mul_dvd_mul_iff_left (by norm_num : (2:ℤ)≠0)).mp hd
      have ht' := ih u v w t d hred hd'
      rw [pow_succ']
      exact mul_dvd_mul_left 2 ht'

theorem three_power_transfer (k : ℕ) (u v w t d : ℤ)
    (h : anchorForm u v w t d=0) (hd : (3:ℤ)^k∣d) : (3:ℤ)^k∣t := by
  induction k generalizing u v w t d with
  | zero => simp
  | succ k ih =>
    have hd3 : (3:ℤ)∣d :=
      dvd_trans (dvd_pow_self 3 (Nat.succ_ne_zero _)) hd
    obtain ⟨hu,hv,hw,ht⟩ := triple_all_of_triple_den u v w t d h hd3
    obtain ⟨u,rfl⟩ := hu
    obtain ⟨v,rfl⟩ := hv
    obtain ⟨w,rfl⟩ := hw
    obtain ⟨t,rfl⟩ := ht
    obtain ⟨d,rfl⟩ := hd3
    have hred : anchorForm u v w t d=0 := by
      rw [anchorForm_scale] at h
      norm_num at h
      exact h
    have hd' : (3:ℤ)^k∣d := by
      rw [pow_succ'] at hd
      exact (mul_dvd_mul_iff_left (by norm_num : (3:ℤ)≠0)).mp hd
    have ht' := ih u v w t d hred hd'
    rw [pow_succ']
    exact mul_dvd_mul_left 3 ht'

/-- Clear denominators without assuming any integral conic witnesses. -/
theorem homogeneous_normalization (u v w t : ℚ)
    (h : u^2+6*v^2-2*w^2-3*t^2+2=0) :
    ∃ U V W T D : ℤ, D≠0 ∧ (T:ℚ)=(D:ℚ)*t ∧ anchorForm U V W T D=0 := by
  let D : ℤ := (u.den:ℤ)*v.den*w.den*t.den
  let U : ℤ := u.num*v.den*w.den*t.den
  let V : ℤ := v.num*u.den*w.den*t.den
  let W : ℤ := w.num*u.den*v.den*t.den
  let T : ℤ := t.num*u.den*v.den*w.den
  have hd : D≠0 := by
    dsimp [D]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by exact_mod_cast u.den_ne_zero)
      (by exact_mod_cast v.den_ne_zero)) (by exact_mod_cast w.den_ne_zero))
      (by exact_mod_cast t.den_ne_zero)
  have hu : (U:ℚ)=(D:ℚ)*u := by
    dsimp [U,D]
    push_cast
    rw [←Rat.mul_den_eq_num u]
    ring
  have hv : (V:ℚ)=(D:ℚ)*v := by
    dsimp [V,D]
    push_cast
    rw [←Rat.mul_den_eq_num v]
    ring
  have hw : (W:ℚ)=(D:ℚ)*w := by
    dsimp [W,D]
    push_cast
    rw [←Rat.mul_den_eq_num w]
    ring
  have ht : (T:ℚ)=(D:ℚ)*t := by
    dsimp [T,D]
    push_cast
    rw [←Rat.mul_den_eq_num t]
    ring
  refine ⟨U,V,W,T,D,hd,ht,?_⟩
  have hQ : (U:ℚ)^2+6*(V:ℚ)^2-2*(W:ℚ)^2-3*(T:ℚ)^2+2*(D:ℚ)^2=0 := by
    rw [hu,hv,hw,ht]
    linear_combination (D:ℚ)^2*h
  unfold anchorForm
  exact_mod_cast hQ

theorem integral_of_power_transfer (p : ℕ) [Fact p.Prime]
    (t : ℚ) (T D : ℤ) (hd : D≠0) (hT : (T:ℚ)=(D:ℚ)*t)
    (hpow : ∀k,(p:ℤ)^k∣D → (p:ℤ)^k∣T) : 0≤padicValRat p t := by
  by_cases ht : t=0
  · simp [ht]
  have hdQ : (D:ℚ)≠0 := by exact_mod_cast hd
  have hT0 : T≠0 := by
    intro hz
    have hh : (D:ℚ)*t=0 := by simpa [hz] using hT.symm
    exact mul_ne_zero hdQ ht hh
  have hdiv := hpow (padicValInt p D) (padicValInt_dvd D)
  have hle : padicValInt p D≤padicValInt p T :=
    ((padicValInt_dvd_iff _ _).mp hdiv).resolve_left hT0
  have hv := congrArg (padicValRat p) hT
  rw [padicValRat.mul hdQ ht,padicValRat.of_int,padicValRat.of_int] at hv
  omega

/-- Soundness of the exact three-variable semilocal conic, without invoking
quaternion classification or ABHN. Completeness is not asserted here. -/
theorem semilocal_conic_sound (u v w t : ℚ)
    (h : u^2+6*v^2-2*w^2-3*t^2+2=0) :
    0≤padicValRat 2 t ∧ 0≤padicValRat 3 t := by
  obtain ⟨U,V,W,T,D,hd,hT,hhom⟩ := homogeneous_normalization u v w t h
  constructor
  · letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
    apply integral_of_power_transfer 2 t T D hd hT
    intro k hk
    exact two_power_transfer k U V W T D hhom hk
  · letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    apply integral_of_power_transfer 3 t T D hd hT
    intro k hk
    exact three_power_transfer k U V W T D hhom hk

/-- The literal scaled anchor row forces the physical quotient to be integral
at two and three. No sign assumption is used. -/
theorem scaled_anchor_sound (u v w A S : ℚ) (hS : S≠0)
    (h : u^2+6*v^2-2*w^2-3*A^2+2*S^2=0) :
    0≤padicValRat 2 (A/S) ∧ 0≤padicValRat 3 (A/S) := by
  apply semilocal_conic_sound (u/S) (v/S) (w/S) (A/S)
  field_simp
  linear_combination h

/-- Valuation-ring closure, with the convention v(0)=0 handled explicitly. -/
theorem integral_sub (p : ℕ) [Fact p.Prime] (a b : ℚ)
    (ha : 0≤padicValRat p a) (hb : 0≤padicValRat p b) :
    0≤padicValRat p (a-b) := by
  by_cases hz : a-b=0
  · simp [hz]
  have hsum : a+ -b≠0 := by simpa [sub_eq_add_neg] using hz
  have hmin := padicValRat.min_le_padicValRat_add (p:=p) hsum
  simp only [padicValRat.neg] at hmin
  exact (le_min ha hb).trans (by simpa [sub_eq_add_neg] using hmin)

/-- The actual affine anchor forces all four labels odd once the two stated
elliptic valuation identities are supplied. No semilocal-conic premise remains. -/
theorem affine_anchor_forces_odd_labels (u v w nR N S : ℚ) (labels : Fin 4 → ℤ)
    (hS : S≠0) (hn : ∀i,labels i≠0)
    (hbase : 0≤padicValRat 2 (nR/S))
    (hnorm : padicValRat 2 (4096*N)= -2*(∑i,(padicValInt 2 (labels i):ℤ)))
    (hrow : u^2+6*v^2-2*w^2-3*(nR+4096*S*N)^2+2*S^2=0) :
    ∀i,Odd (labels i) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hphysical := (scaled_anchor_sound u v w (nR+4096*S*N) S hS hrow).1
  have heq : (nR+4096*S*N)/S-nR/S=4096*N := by field_simp; ring
  have hnorm0 := integral_sub 2 _ _ hphysical hbase
  rw [heq,hnorm] at hnorm0
  have hnonneg : 0≤∑i,(padicValInt 2 (labels i):ℤ) :=
    Finset.sum_nonneg (fun i _ => Int.natCast_nonneg _)
  have hsum : (∑i,(padicValInt 2 (labels i):ℤ))=0 := by omega
  have hzeros := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i (_:i∈Finset.univ) => Int.natCast_nonneg (padicValInt 2 (labels i)))).mp hsum
  intro i
  have hz : padicValInt 2 (labels i)=0 := by exact_mod_cast hzeros i (Finset.mem_univ i)
  have hndiv : ¬(2:ℤ)∣labels i := by
    simpa [hn i] using padicValInt.eq_zero_iff.mp hz
  exact Int.not_even_iff_odd.mp (fun he => hndiv (even_iff_two_dvd.mp he))

/-- After oddness makes the added norm term 3-integral, the same physical
anchor gives the original scalar 3-adic condition. -/
theorem affine_anchor_scalar_three (u v w nR N S : ℚ)
    (hS : S≠0) (hN : 0≤padicValRat 3 (4096*N))
    (hrow : u^2+6*v^2-2*w^2-3*(nR+4096*S*N)^2+2*S^2=0) :
    0≤padicValRat 3 (nR/S) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hphysical := (scaled_anchor_sound u v w (nR+4096*S*N) S hS hrow).2
  have heq : (nR+4096*S*N)/S-4096*N=nR/S := by field_simp; ring
  have hh := integral_sub 3 _ _ hphysical hN
  simpa [heq] using hh

end SemilocalAnchor318
