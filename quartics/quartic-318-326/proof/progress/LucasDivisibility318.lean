module
public import LucasSequence318
public section
namespace LucasSequence318

 theorem index_divisible (a d : ℤ) (n : ℕ)
    (hd : d=a-2 ∨ d=a+2) (hu : d ∣ U a n) : d ∣ (n:ℤ) := by
  rcases hd with rfl | rfl
  · exact dvd_sub hu (mod_minus a n) |>.trans (by simp)
  · have h := dvd_sub (mod_plus a n) (dvd_mul_of_dvd_right hu ((-1:ℤ)^n))
    simpa only [add_sub_cancel_left] using h

 theorem abs_norm_solution (a t w : ℤ) (ha : 0<a) (hw : w≠0)
    (heq : t^2-a*t*w+w^2=1) : |t|^2-a*|t| * |w|+|w|^2=1 := by
  have hw1 : 1≤w^2 := by nlinarith [sq_pos_of_ne_zero hw]
  have htw : 0≤t*w := by
    by_contra h
    have hp := mul_neg_of_pos_of_neg ha (show t*w<0 by omega)
    nlinarith [sq_nonneg t]
  have hab : |t| * |w|=t*w := by rw [←abs_mul,abs_of_nonneg htw]
  rw [sq_abs,sq_abs]
  nlinarith only [heq,congrArg (fun x:ℤ => a*x) hab]

/-- The congruence obstruction forces a large index in every nontrivial
norm-one solution with its second coordinate divisible by a±2. -/
theorem divisible_solution_growth (a t w d : ℤ) (ha : 7≤a)
    (ht : 0≤t) (hw : 0<w) (hd : d=a-2 ∨ d=a+2) (hdw : d∣w)
    (heq : t^2-a*t*w+w^2=1) :
    ∃ m : ℕ, a-4≤(m:ℤ) ∧ (a-1)^m≤t := by
  have hd5 : 5≤d := by rcases hd with rfl|rfl <;> omega
  have htn : (t.toNat:ℤ)=t := Int.toNat_of_nonneg ht
  have hwn : (w.toNat:ℤ)=w := Int.toNat_of_nonneg hw.le
  have hne : t≠w := by
    intro h
    subst t
    have hp := mul_nonneg (show 0≤a-2 by omega) (sq_nonneg w)
    nlinarith only [heq,hp]
  rcases lt_or_gt_of_ne hne with htw | hwt
  · have hlt : t.toNat<w.toNat := by exact_mod_cast (show (t.toNat:ℤ)<w.toNat by omega)
    have hnrm : (t.toNat:ℤ)^2-a*t.toNat*w.toNat+w.toNat^2=1 := by
      simpa only [htn,hwn] using heq
    obtain ⟨n,hn0,hn1⟩ := ordered_solution a (by omega) w.toNat t.toNat hlt hnrm
    rw [htn] at hn0
    rw [hwn] at hn1
    have hdiv := index_divisible a d (n+1) hd (hn1 ▸ hdw)
    have hdn : d≤(n+1:ℕ) := Int.le_of_dvd (by omega) hdiv
    have hnpos : 0<n := by omega
    refine ⟨n-1,by rcases hd with rfl|rfl <;> omega,?_⟩
    have h := (U_growth a (by omega) (n-1)).2.2
    rwa [Nat.sub_add_cancel hnpos,hn0] at h
  · have hlt : w.toNat<t.toNat := by exact_mod_cast (show (w.toNat:ℤ)<t.toNat by omega)
    have hnrm : (w.toNat:ℤ)^2-a*w.toNat*t.toNat+t.toNat^2=1 := by
      rw [htn,hwn]
      nlinarith only [heq]
    obtain ⟨n,hn0,hn1⟩ := ordered_solution a (by omega) t.toNat w.toNat hlt hnrm
    rw [hwn] at hn0
    rw [htn] at hn1
    have hnpos : 0<n := by
      by_contra h
      have hn : n=0 := by omega
      subst n
      simp only [U_zero] at hn0
      omega
    have hdiv := index_divisible a d n hd (hn0 ▸ hdw)
    have hdn : d≤(n:ℤ) := Int.le_of_dvd (by omega) hdiv
    refine ⟨n,by rcases hd with rfl|rfl <;> omega,?_⟩
    simpa only [hn1] using (U_growth a (by omega) n).2.2

/-- Normalization of the literal signed Lucas equation, including s<0. -/
theorem literal_growth (s t z : ℤ) (hs : 7≤|s|) (hz : z≠0)
    (heq : t^2-s*(s-2)*t*z+(s-2)^2*z^2=1) :
    ∃ m : ℕ, |s|-4≤(m:ℤ) ∧ (|s|-1)^m≤|t| := by
  let w : ℤ := s.sign*(s-2)*z
  have hs0 : s≠0 := by intro h; simp [h] at hs
  have hs2 : s-2≠0 := by
    intro h
    have hsval : s=2 := by omega
    norm_num [hsval] at hs
  have hw0 : w≠0 := mul_ne_zero (mul_ne_zero (fun h => hs0 (Int.eq_zero_of_sign_eq_zero h)) hs2) hz
  have hsabs : |s.sign|=1 := by
    rcases Int.sign_trichotomy s with h|h|h
    · rw [h]; norm_num
    · exact False.elim (hs0 (Int.eq_zero_of_sign_eq_zero h))
    · rw [h]; norm_num
  have habs : |w|=|s-2| * |z| := by
    dsimp [w]
    rw [abs_mul,abs_mul,hsabs,one_mul]
  have hsign : |s| * s.sign=s := by simpa [mul_comm] using Int.sign_mul_abs s
  have hsignsq : s.sign^2=1 := by
    rcases Int.sign_trichotomy s with h|h|h
    · rw [h]; norm_num
    · exact False.elim (hs0 (Int.eq_zero_of_sign_eq_zero h))
    · rw [h]; norm_num
  have hnorm : t^2-|s| * t*w+w^2=1 := by
    dsimp [w]
    nlinarith only [heq,congrArg (fun x:ℤ => x*(s-2)*t*z) hsign,
      congrArg (fun x:ℤ => x*(s-2)^2*z^2) hsignsq]
  have hmod : |s-2|=|s|-2 ∨ |s-2|=|s|+2 := by
    rcases le_total 0 s with h|h
    · left; rw [abs_of_nonneg h] at hs ⊢; rw [abs_of_nonneg (by omega)]
    · right; rw [abs_of_nonpos h,abs_of_nonpos (by omega)]; ring
  exact divisible_solution_growth |s| |t| |w| |s-2| hs (abs_nonneg t)
    (abs_pos.mpr hw0) hmod (by rw [habs]; exact dvd_mul_right _ _)
    (abs_norm_solution |s| t w (by omega) hw0 hnorm)

end LucasSequence318
