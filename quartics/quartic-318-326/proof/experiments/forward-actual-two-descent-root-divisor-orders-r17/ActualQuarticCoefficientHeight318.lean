module
public import ActualQuarticEliminantHeight318
public section
noncomputable section
namespace ActualQuarticCoefficientHeight318
open TernaryQuadraticLineCover318 ActualAffineQuarticEliminant318
open OriginalUniformEliminantHeight318 OriginalAffineSieveEliminants318
set_option maxHeartbeats 12000000

@[expose] def innerHeight (κ t : ℤ) (L : ℝ) := (2*|(κ:ℝ)|+2)*L^2+(t:ℝ)^2+2*|(t:ℝ)|
@[expose] def quarticHeight (κ t : ℤ) (L : ℝ) := 8*((innerHeight κ t L)^2+(t:ℝ)^2*L^2)
@[expose] def coefficientHeight (κ t : ℤ) (L : ℝ) := 1+formHeight κ t L+quarticHeight κ t L

lemma inner_bounds (κ t : ℤ) (a d : Vector ℤ) (L : ℝ) (hL : 0≤L)
    (ha : Box a L) (hd : Box d L) :
    |(r2 κ d:ℝ)|≤ innerHeight κ t L ∧ |(r1 κ a d:ℝ)|≤ innerHeight κ t L ∧
    |(r0 κ t a:ℝ)|≤ innerHeight κ t L := by
  have haw := square_bound a.2.2 L ha.2.2
  have hdw := square_bound d.2.2 L hd.2.2
  have hxz := product_bound a.1 d.2.1 L hL ha.1 hd.2.1
  have hzx := product_bound d.1 a.2.1 L hL hd.1 ha.2.1
  have haa := product_bound a.1 a.2.1 L hL ha.1 ha.2.1
  have hdd := product_bound d.1 d.2.1 L hL hd.1 hd.2.1
  have hww := product_bound a.2.2 d.2.2 L hL ha.2.2 hd.2.2
  have hκ0 := abs_nonneg (κ:ℝ)
  have ht0 := abs_nonneg (t:ℝ)
  have hL0 := sq_nonneg L
  have ht2 := sq_nonneg (t:ℝ)
  have bound (x y : ℤ) (hx : |(x:ℝ)|≤L^2) (hy : |(y:ℝ)|≤L^2) :
      |((κ*x-y:ℤ):ℝ)|≤(|(κ:ℝ)|+1)*L^2 := by
    push_cast
    calc
      _ ≤ |(κ:ℝ)|*|(x:ℝ)|+|(y:ℝ)| := by simpa only [abs_mul] using abs_sub ((κ:ℝ)*x) y
      _ ≤ |(κ:ℝ)|*L^2+L^2 := by gcongr
      _ = _ := by ring
  have hr2 := bound _ _ hdw hdd
  have hr0 := bound _ _ haw haa
  have hb1 : |((2*κ*(a.2.2*d.2.2):ℤ):ℝ)|≤2*|(κ:ℝ)|*L^2 := by
    push_cast
    simp only [abs_mul,abs_ofNat]
    simpa only [Int.cast_mul,abs_mul,mul_assoc] using
      mul_le_mul_of_nonneg_left hww (show 0≤2*|(κ:ℝ)| by positivity)
  have hsum : |((2*κ*(a.2.2*d.2.2)-a.1*d.2.1-d.1*a.2.1:ℤ):ℝ)|≤
      (2*|(κ:ℝ)|+2)*L^2 := by
    have h1 := abs_sub ((2*κ*(a.2.2*d.2.2)-a.1*d.2.1:ℤ):ℝ) ((d.1*a.2.1:ℤ):ℝ)
    have h2 := abs_sub ((2*κ*(a.2.2*d.2.2):ℤ):ℝ) ((a.1*d.2.1:ℤ):ℝ)
    push_cast only [Int.cast_sub] at h1 h2 ⊢
    linarith only [h1,h2,hb1,hxz,hzx]
  have hc0 : |((κ*a.2.2^2-a.1*a.2.1+t^2+2*t:ℤ):ℝ)|≤
      (|(κ:ℝ)|+1)*L^2+(t:ℝ)^2+2*|(t:ℝ)| := by
    have h1 := abs_add ((κ*a.2.2^2-a.1*a.2.1+t^2:ℤ):ℝ) ((2*t:ℤ):ℝ)
    have h2 := abs_add ((κ*a.2.2^2-a.1*a.2.1:ℤ):ℝ) ((t^2:ℤ):ℝ)
    push_cast at h1 h2 ⊢
    simp only [abs_pow,abs_mul,abs_ofNat,sq_abs] at h1 h2
    push_cast at hr0
    linarith only [h1,h2,hr0]
  have hr1 : |(r1 κ a d:ℝ)|≤(2*|(κ:ℝ)|+2)*L^2 := by
    convert hsum using 1 <;> simp only [r1] <;> push_cast <;> ring
  have hj : 0≤(|(κ:ℝ)|+1)*L^2 := by positivity
  refine ⟨?_,?_,?_⟩
  · change |((κ*d.2.2^2-d.1*d.2.1:ℤ):ℝ)|≤ innerHeight κ t L
    dsimp [innerHeight]
    linarith only [hr2,hj,ht2,ht0]
  · dsimp [innerHeight]
    linarith only [hr1,ht2,ht0]
  · change |((κ*a.2.2^2-a.1*a.2.1+t^2+2*t:ℤ):ℝ)|≤ innerHeight κ t L
    push_cast
    dsimp [innerHeight]
    linarith only [hc0,hj]

lemma quartic_bounds (κ t : ℤ) (a d : Vector ℤ) (L : ℝ) (hL : 0≤L)
    (ha : Box a L) (hd : Box d L) :
    |(k4 κ a d:ℝ)|≤quarticHeight κ t L ∧ |(k3 κ a d:ℝ)|≤quarticHeight κ t L ∧
    |(k2 κ t a d:ℝ)|≤quarticHeight κ t L ∧ |(k1 κ t a d:ℝ)|≤quarticHeight κ t L ∧
    |(k0 κ t a d:ℝ)|≤quarticHeight κ t L := by
  obtain ⟨hr2,hr1,hr0⟩ := inner_bounds κ t a d L hL ha hd
  let J := innerHeight κ t L
  have hJ : 0≤J := by dsimp [J,innerHeight];positivity
  have hsa : |((a.1+a.2.1:ℤ):ℝ)|≤2*L := by
    push_cast
    exact (abs_add _ _).trans (by linarith [ha.1,ha.2.1])
  have hsd : |((d.1+d.2.1:ℤ):ℝ)|≤2*L := by
    push_cast
    exact (abs_add _ _).trans (by linarith [hd.1,hd.2.1])
  have power (x : ℤ) (hx : |(x:ℝ)|≤J) : |((x^2:ℤ):ℝ)|≤J^2 := by
    push_cast
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) hx 2
  have product (x y : ℤ) (hx : |(x:ℝ)|≤J) (hy : |(y:ℝ)|≤J) :
      |((2*x*y:ℤ):ℝ)|≤2*J^2 := by
    push_cast
    simp only [abs_mul,abs_ofNat]
    calc
      _ ≤ 2*J*J := by gcongr
      _ = _ := by ring
  have hp2 := power _ hr2
  have hp1 := power _ hr1
  have hp0 := power _ hr0
  have hp21 := product _ _ hr2 hr1
  have hp20 := product _ _ hr2 hr0
  have hp10 := product _ _ hr1 hr0
  push_cast at hsa hsd
  have hsqd : |((t^2*(d.1+d.2.1)^2:ℤ):ℝ)|≤4*(t:ℝ)^2*L^2 := by
    push_cast
    rw [abs_mul,abs_of_nonneg (sq_nonneg (t:ℝ)),abs_pow]
    calc
      _ ≤ (t:ℝ)^2*(2*L)^2 := by gcongr
      _ = _ := by ring
  have hsqa : |((t^2*(a.1+a.2.1)^2:ℤ):ℝ)|≤4*(t:ℝ)^2*L^2 := by
    push_cast
    rw [abs_mul,abs_of_nonneg (sq_nonneg (t:ℝ)),abs_pow]
    calc
      _ ≤ (t:ℝ)^2*(2*L)^2 := by gcongr
      _ = _ := by ring
  have hcross : |((2*t^2*(a.1+a.2.1)*(d.1+d.2.1):ℤ):ℝ)|≤8*(t:ℝ)^2*L^2 := by
    push_cast
    simp only [abs_mul,abs_pow,abs_ofNat]
    rw [sq_abs (t:ℝ)]
    calc
      _ ≤ 2*(t:ℝ)^2*(2*L)*(2*L) := by gcongr
      _ = _ := by ring
  have hj2 := sq_nonneg J
  have htL := mul_nonneg (sq_nonneg (t:ℝ)) (sq_nonneg L)
  have hk2a := abs_add (((r1 κ a d)^2+2*r2 κ d*r0 κ t a:ℤ):ℝ) ((t^2*(d.1+d.2.1)^2:ℤ):ℝ)
  have hk2b := abs_add (((r1 κ a d)^2:ℤ):ℝ) ((2*r2 κ d*r0 κ t a:ℤ):ℝ)
  have hk1 := abs_add ((2*r1 κ a d*r0 κ t a:ℤ):ℝ) ((2*t^2*(a.1+a.2.1)*(d.1+d.2.1):ℤ):ℝ)
  have hk0 := abs_add (((r0 κ t a)^2:ℤ):ℝ) ((t^2*(a.1+a.2.1)^2:ℤ):ℝ)
  dsimp [k4,k3,k2,k1,k0,quarticHeight]
  change _≤8*(J^2+(t:ℝ)^2*L^2) ∧ _≤8*(J^2+(t:ℝ)^2*L^2) ∧
    _≤8*(J^2+(t:ℝ)^2*L^2) ∧ _≤8*(J^2+(t:ℝ)^2*L^2) ∧ _≤8*(J^2+(t:ℝ)^2*L^2)
  push_cast only [Int.cast_add] at hk2a hk2b hk1 hk0 ⊢
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith⟩

end ActualQuarticCoefficientHeight318
