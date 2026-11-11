module
public import OriginalOffsetZeroLocus318
public section
noncomputable section
namespace OriginalUniformEliminantHeight318
open TernaryQuadraticLineCover318 LiteralAdjacentNormSlice318
open OriginalAffineSieveEliminants318 OriginalQuadraticEliminant318
set_option maxHeartbeats 6500000

@[expose] def Box (a : Vector ℤ) (L : ℝ) : Prop :=
  |(a.1:ℝ)|≤L ∧ |(a.2.1:ℝ)|≤L ∧ |(a.2.2:ℝ)|≤L
@[expose] def formHeight (κ t : ℤ) (L : ℝ) :=
  (2*|(κ:ℝ)|*(|(t:ℝ)|+2)+4)*L^2+2*|(t:ℝ)|
@[expose] def factorHeight (t : ℤ) (L : ℝ) := 2*L^2+(t:ℝ)^2
@[expose] def regularHeight (κ t : ℤ) (L : ℝ) := 8*(formHeight κ t L)^2*(factorHeight t L)^2
@[expose] def exceptionalHeight (t : ℤ) (L : ℝ) := 4*L^4+(t:ℝ)^2*L^2

lemma product_bound (x y : ℤ) (L : ℝ) (hL : 0≤L)
    (hx : |(x:ℝ)|≤L) (hy : |(y:ℝ)|≤L) : |((x*y:ℤ):ℝ)|≤L^2 := by
  push_cast
  rw [abs_mul,pow_two]
  exact mul_le_mul hx hy (abs_nonneg _) hL

lemma square_bound (x : ℤ) (L : ℝ) (hx : |(x:ℝ)|≤L) : |((x^2:ℤ):ℝ)|≤L^2 := by
  push_cast
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hx _

/-- Uniform actual integer coefficient budgets on the entire enlarged
offset rectangle. All three coefficients of BOTH original forms are kept. -/
theorem form_coefficients (side : Bool) (κ t : ℤ) (a d : Vector ℤ) (L : ℝ)
    (hL : 0≤L) (ha : Box a L) (hd : Box d L) :
    |(fA side κ t d:ℝ)|≤formHeight κ t L ∧
    |(fB side κ t a d:ℝ)|≤formHeight κ t L ∧
    |(fC side κ t a:ℝ)|≤formHeight κ t L := by
  have hκ0 := abs_nonneg (κ:ℝ)
  have ht0 := abs_nonneg (t:ℝ)
  have hκt : |((κ*(t+2):ℤ):ℝ)|≤|(κ:ℝ)|*(|(t:ℝ)|+2) := by
    push_cast
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((abs_add _ _).trans (by norm_num)) hκ0
  have hww := product_bound a.2.2 d.2.2 L hL ha.2.2 hd.2.2
  have hxz := product_bound a.1 d.2.1 L hL ha.1 hd.2.1
  have hzx := product_bound d.1 a.2.1 L hL hd.1 ha.2.1
  have hdd := product_bound d.1 d.2.1 L hL hd.1 hd.2.1
  have haa := product_bound a.1 a.2.1 L hL ha.1 ha.2.1
  have hdw := square_bound d.2.2 L hd.2.2
  have haw := square_bound a.2.2 L ha.2.2
  have first (x : ℤ) (hx : |(x:ℝ)|≤L^2) :
      |((κ*x:ℤ):ℝ)|≤|(κ:ℝ)|*L^2 := by
    push_cast
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hx hκ0
  have second (x : ℤ) (hx : |(x:ℝ)|≤L^2) :
      |((κ*(t+2)*x:ℤ):ℝ)|≤|(κ:ℝ)|*(|(t:ℝ)|+2)*L^2 := by
    push_cast at hκt ⊢
    rw [abs_mul]
    exact mul_le_mul hκt hx (abs_nonneg _) (by positivity)
  have h1 := first _ hdw
  have h2 := first _ hww
  have h3 := first _ haw
  have h4 := second _ hdw
  have h5 := second _ hww
  have h6 := second _ haw
  have bound : 0≤|(κ:ℝ)|*|(t:ℝ)|*L^2 := by positivity
  have bound2 : 0≤|(κ:ℝ)|*L^2 := by positivity
  have Lsq := sq_nonneg L
  push_cast at h1 h2 h3 h4 h5 h6 hww hxz hzx hdd haa hdw haw
  simp only [abs_mul,abs_pow,sq_abs] at h1 h2 h3 h4 h5 h6 hww hxz hzx hdd haa hdw haw
  cases side
  · refine ⟨?_,?_,?_⟩
    · change |((κ*d.2.2^2:ℤ):ℝ)|≤_
      dsimp [formHeight]
      nlinarith
    · have he : fB false κ t a d=2*(κ*(a.2.2*d.2.2)) := by simp [fB];ring
      rw [he,Int.cast_mul,abs_mul]
      norm_num
      push_cast
      simp only [abs_mul,abs_pow,sq_abs]
      dsimp [formHeight]
      nlinarith
    · have hh := abs_add (((κ*a.2.2^2:ℤ):ℝ)) ((2*t:ℤ):ℝ)
      change |((κ*a.2.2^2+2*t:ℤ):ℝ)|≤_
      push_cast at hh ⊢
      simp only [abs_mul,abs_pow,sq_abs,abs_ofNat] at hh
      dsimp [formHeight]
      push_cast at h3
      nlinarith
  · refine ⟨?_,?_,?_⟩
    · have hh := abs_sub (((κ*(t+2)*d.2.2^2:ℤ):ℝ)) ((2*(d.1*d.2.1):ℤ):ℝ)
      change |((κ*(t+2)*d.2.2^2-2*d.1*d.2.1:ℤ):ℝ)|≤_
      push_cast at hh h4 hdd ⊢
      simp only [abs_mul,abs_pow,sq_abs,abs_ofNat] at hh
      dsimp [formHeight]
      nlinarith
    · have he : fB true κ t a d=2*(κ*(t+2)*(a.2.2*d.2.2))-2*(a.1*d.2.1+d.1*a.2.1) := by simp [fB];ring
      have hh := abs_sub ((2*(κ*(t+2)*(a.2.2*d.2.2)):ℤ):ℝ) ((2*(a.1*d.2.1+d.1*a.2.1):ℤ):ℝ)
      have hs := abs_add ((a.1*d.2.1:ℤ):ℝ) ((d.1*a.2.1:ℤ):ℝ)
      rw [he]
      push_cast at hh hs h5 hxz hzx ⊢
      simp only [abs_mul,abs_pow,sq_abs,abs_ofNat] at hh
      dsimp [formHeight]
      nlinarith
    · have hh := abs_sub (((κ*(t+2)*a.2.2^2:ℤ):ℝ)) ((2*(a.1*a.2.1):ℤ):ℝ)
      change |((κ*(t+2)*a.2.2^2-2*a.1*a.2.1:ℤ):ℝ)|≤_
      push_cast at hh h6 haa ⊢
      simp only [abs_mul,abs_pow,sq_abs,abs_ofNat] at hh
      dsimp [formHeight]
      nlinarith

lemma norm_coefficients (t x d : ℤ) (L : ℝ) (hL : 0≤L)
    (hx : |(x:ℝ)|≤L) (hd : |(d:ℝ)|≤L) :
    |((d^2:ℤ):ℝ)|≤factorHeight t L ∧
    |((2*x*d:ℤ):ℝ)|≤factorHeight t L ∧
    |((x^2+t^2:ℤ):ℝ)|≤factorHeight t L := by
  have h1 := square_bound d L hd
  have h2 := product_bound x d L hL hx hd
  have h3 := square_bound x L hx
  have h4 := abs_add ((x^2:ℤ):ℝ) ((t^2:ℤ):ℝ)
  dsimp [factorHeight]
  push_cast at h1 h2 h3 h4 ⊢
  simp only [abs_mul,abs_pow,sq_abs,abs_ofNat] at *
  refine ⟨by nlinarith [sq_nonneg L,sq_nonneg (t:ℝ)],?_,?_⟩
  · nlinarith [sq_nonneg (t:ℝ)]
  · nlinarith [sq_nonneg L]

/-- Actual regular eliminant height, uniform in both original norm
factors and both original pairs. No numerical height oracle is supplied. -/
theorem actual_regular_height (side coordinate : Bool) (κ t : ℤ) (a d : Vector ℤ)
    (L : ℝ) (hL : 0≤L) (ha : Box a L) (hd : Box d L) :
    |(normEliminant side κ t a d coordinate:ℝ)|≤regularHeight κ t L := by
  obtain ⟨hA,hB,hC⟩ := form_coefficients side κ t a d L hL ha hd
  have hcoord : |((if coordinate then a.2.1 else a.1:ℤ):ℝ)|≤L ∧
      |((if coordinate then d.2.1 else d.1:ℤ):ℝ)|≤L := by
    cases coordinate
    · exact ⟨ha.1,hd.1⟩
    · exact ⟨ha.2.1,hd.2.1⟩
  obtain ⟨he,hf,hg⟩ := norm_coefficients t _ _ L hL hcoord.1 hcoord.2
  exact eliminant_abs_bound _ _ _ _ _ _ (formHeight κ t L) (factorHeight t L)
    (by dsimp [formHeight];positivity) (by dsimp [factorHeight];positivity) hA hB hC he hf hg

/-- The exceptional unpadded eliminant has its OWN explicit bound. -/
theorem actual_exceptional_height (t x z dx dz : ℤ) (L : ℝ) (hL : 0≤L)
    (hx : |(x:ℝ)|≤L) (hz : |(z:ℝ)|≤L) (hdx : |(dx:ℝ)|≤L) (hdz : |(dz:ℝ)|≤L) :
    |(OriginalLinearNormEliminant318.eliminant t x z dx dz:ℝ)|≤exceptionalHeight t L := by
  have h1 := product_bound dx z L hL hdx hz
  have h2 := product_bound dz x L hL hdz hx
  have hs : |((dx*z-dz*x:ℤ):ℝ)|≤2*L^2 := by
    exact (by simpa only [Int.cast_sub] using abs_sub ((dx*z:ℤ):ℝ) ((dz*x:ℤ):ℝ)).trans (by linarith)
  have hs2 := pow_le_pow_left₀ (abs_nonneg _) hs 2
  have hdx2 := square_bound dx L hdx
  have hh := mul_le_mul_of_nonneg_left hdx2 (sq_nonneg (t:ℝ))
  push_cast [OriginalLinearNormEliminant318.eliminant]
  rw [abs_of_nonneg (by positivity)]
  dsimp [exceptionalHeight]
  push_cast at hs2 hh
  simp only [abs_pow,sq_abs] at hs2 hh
  nlinarith only [hs2,hh]

end OriginalUniformEliminantHeight318
