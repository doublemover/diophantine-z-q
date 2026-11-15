module
public import ConcreteG8Domain
public import SemilocalAnchor318
public section
namespace AnchorNorm318
open ConcreteG8Domain
set_option maxHeartbeats 0

@[expose] abbrev norm (x : K) : ℚ := QuadraticAlgebra.norm x

@[simp] theorem norm_pair (a b : ℚ) : norm (pair a b)=a^2-2*b^2 := by
  simp [norm,QuadraticAlgebra.norm_def,pair]
  ring

@[simp] theorem norm_mul (x y : K) : norm (x*y)=norm x*norm y := map_mul _ _ _
@[simp] theorem norm_pow (x : K) (n : ℕ) : norm (x^n)=norm x^n := map_pow _ _ _

theorem norm_ne_zero {x : K} (hx : x≠0) : norm x≠0 :=
  (QuadraticAlgebra.isUnit_iff_norm_isUnit.mp (isUnit_iff_ne_zero.mpr hx)).ne_zero

@[simp] theorem norm_inv (x : K) : norm x⁻¹=(norm x)⁻¹ := by
  by_cases hx : x=0
  · simp [hx,norm]
  · rw [inv_eq_one_div (norm x)]
    apply (eq_div_iff (norm_ne_zero hx)).mpr
    rw [←norm_mul,inv_mul_cancel₀ hx]
    exact map_one _

@[simp] theorem norm_div (x y : K) : norm (x/y)=norm x/norm y := by
  simp [div_eq_mul_inv]

/-- The ramified quadratic norm: its rational 2-valuation is twice the
normalized local valuation. Opposite coefficient parity prevents cancellation. -/
theorem norm_two_value (a b : ℚ) (ha : a≠0) (hb : b≠0) :
    padicValRat 2 (norm (pair a b))=
      min (2*padicValRat 2 a) (1+2*padicValRat 2 b) := by
  letI : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hn : a^2-2*b^2≠0 := ConcreteQuadraticDomains.norm_nonzero_of_real_nonzero a b ha
  have ht : padicValRat 2 (2:ℚ)=1 := padicValRat.self (by norm_num)
  have hv : padicValRat 2 (-(2*b^2))=1+2*padicValRat 2 b := by
    rw [padicValRat.neg,padicValRat.mul (by norm_num) (pow_ne_zero _ hb),ht,padicValRat.pow]
    norm_num
  have he := padicValRat.add_eq_min (p:=2) (q:=a^2) (r:=-(2*b^2))
    (by simpa [sub_eq_add_neg] using hn) (pow_ne_zero _ ha)
    (neg_ne_zero.mpr (mul_ne_zero (by norm_num) (pow_ne_zero _ hb)))
    (by rw [padicValRat.pow,hv]; norm_num; omega)
  simpa only [norm_pair,sub_eq_add_neg,padicValRat.pow,hv,Nat.cast_ofNat] using he

/-- A direct conversion from a nonzero square abscissa to its root-norm
valuation. This is the exact normalization used by raw coordinate 145. -/
theorem root_norm_value (p : ℕ) [Fact p.Prime] (h x : K) (hx : h^2=x)
    (v : ℤ) (hval : padicValRat p (norm x)=2*v) :
    padicValRat p (norm h)=v := by
  rw [←hx,norm_pow,padicValRat.pow] at hval
  norm_num at hval
  omega

/-- The scalar chart stores the inverse of the norm of a square root of x,
not the norm of x or the root itself. -/
theorem inverse_root_norm_value (p : ℕ) [Fact p.Prime] (h x : K) (hx : h^2=x)
    (v : ℤ) (hval : padicValRat p (norm x)= -2*v) :
    padicValRat p ((norm h)⁻¹)=v := by
  rw [padicValRat.inv]
  have hh := root_norm_value p h x hx (-v) (by linarith)
  omega

/-- Ordinary rational unit computations, used for exact generator constants. -/
theorem rational_unit_value (p : ℕ) [Fact p.Prime] (a b : ℤ)
    (ha : ¬(p:ℤ)∣a) (hb : ¬(p:ℤ)∣b) :
    padicValRat p ((a:ℚ)/(b:ℚ))=0 := by
  have ha0 : a≠0 := fun h => ha (h ▸ dvd_zero _)
  have hb0 : b≠0 := fun h => hb (h ▸ dvd_zero _)
  rw [padicValRat.div (by exact_mod_cast ha0) (by exact_mod_cast hb0),
    padicValRat.of_int,padicValRat.of_int,
    padicValInt.eq_zero_of_not_dvd ha,padicValInt.eq_zero_of_not_dvd hb]
  norm_num

private theorem three_norm_unit (a b : ℤ) (hab : ¬(3∣a ∧ 3∣b)) :
    ¬3∣a^2-2*b^2 := by
  simp only [Int.dvd_iff_emod_eq_zero] at *
  have ha0 := Int.emod_nonneg a (by norm_num : (3:ℤ)≠0)
  have ha1 := Int.emod_lt_of_pos a (by norm_num : (0:ℤ)<3)
  have hb0 := Int.emod_nonneg b (by norm_num : (3:ℤ)≠0)
  have hb1 := Int.emod_lt_of_pos b (by norm_num : (0:ℤ)<3)
  have he : (a^2-2*b^2)%3=((a%3)^2-2*(b%3)^2)%3 := by
    simp only [pow_two,Int.sub_emod,Int.mul_emod,Int.emod_emod]
  rw [he]
  interval_cases ha : a%3 <;> interval_cases hb : b%3 <;> norm_num at *

/-- Exact inert-prime norm valuation for integral coefficients, proved by
modulo-3 anisotropy rather than a local-field or residue-field assumption. -/
theorem norm_three_int_value (a b : ℤ) (ha : a≠0) (hb : b≠0) :
    padicValRat 3 (((a^2-2*b^2:ℤ):ℚ))=
      2*(min (padicValInt 3 a) (padicValInt 3 b):ℕ) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let k := min (padicValInt 3 a) (padicValInt 3 b)
  have haD : (3:ℤ)^k∣a := (padicValInt_dvd_iff k a).mpr (Or.inr (min_le_left _ _))
  have hbD : (3:ℤ)^k∣b := (padicValInt_dvd_iff k b).mpr (Or.inr (min_le_right _ _))
  obtain ⟨A,hA⟩ := haD
  obtain ⟨B,hB⟩ := hbD
  have hab : ¬(3∣A ∧ 3∣B) := by
    rintro ⟨⟨aa,haa⟩,⟨bb,hbb⟩⟩
    have haD' : (3:ℤ)^(k+1)∣a := ⟨aa,by rw [hA,haa,pow_succ]; ring⟩
    have hbD' : (3:ℤ)^(k+1)∣b := ⟨bb,by rw [hB,hbb,pow_succ]; ring⟩
    have haL := ((padicValInt_dvd_iff (k+1) a).mp haD').resolve_left ha
    have hbL := ((padicValInt_dvd_iff (k+1) b).mp hbD').resolve_left hb
    dsimp [k] at *
    omega
  have hu := three_norm_unit A B hab
  have hu0 : A^2-2*B^2≠0 := fun h => hu (h ▸ dvd_zero _)
  have hvu : padicValRat 3 (((A^2-2*B^2:ℤ):ℚ))=0 := by
    rw [padicValRat.of_int,padicValInt.eq_zero_of_not_dvd hu]
    norm_num
  have he : (((a^2-2*b^2:ℤ):ℚ))=(3:ℚ)^(2*k)*(((A^2-2*B^2:ℤ):ℚ)) := by
    rw [hA,hB]
    push_cast
    rw [show 2*k=k*2 by omega,pow_mul]
    ring
  have h3 : padicValRat 3 (3:ℚ)=1 := padicValRat.self (by norm_num)
  rw [he,padicValRat.mul (by positivity) (by exact_mod_cast hu0),hvu,
    padicValRat.pow,h3]
  norm_num [k]

/-- The inert quadratic norm has twice the minimum rational coefficient
valuation. The hypotheses avoid padicValRat's artificial value at zero. -/
theorem norm_three_value (a b : ℚ) (ha : a≠0) (hb : b≠0) :
    padicValRat 3 (norm (pair a b))=
      2*min (padicValRat 3 a) (padicValRat 3 b) := by
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let A : ℤ := a.num*b.den
  let B : ℤ := b.num*a.den
  let D : ℤ := a.den*b.den
  have hd : D≠0 := by dsimp [D]; positivity
  have had : a.den≠0 := a.den_ne_zero
  have hbd : b.den≠0 := b.den_ne_zero
  have han : a.num≠0 := Rat.num_ne_zero.mpr ha
  have hbn : b.num≠0 := Rat.num_ne_zero.mpr hb
  have hA : A≠0 := mul_ne_zero han (by exact_mod_cast hbd)
  have hB : B≠0 := mul_ne_zero hbn (by exact_mod_cast had)
  have haeq : (A:ℚ)=a*(D:ℚ) := by
    dsimp [A,D]
    push_cast
    rw [←mul_assoc,Rat.mul_den_eq_num]
  have hbeq : (B:ℚ)=b*(D:ℚ) := by
    dsimp [B,D]
    push_cast
    rw [mul_left_comm b,←Rat.mul_den_eq_num]
    ring
  have hvA : (padicValInt 3 A:ℤ)=padicValRat 3 a+padicValRat 3 (D:ℚ) := by
    rw [←padicValRat.of_int,haeq,padicValRat.mul ha (by exact_mod_cast hd)]
  have hvB : (padicValInt 3 B:ℤ)=padicValRat 3 b+padicValRat 3 (D:ℚ) := by
    rw [←padicValRat.of_int,hbeq,padicValRat.mul hb (by exact_mod_cast hd)]
  have hq : norm (pair a b)≠0 := by
    simpa only [norm_pair] using ConcreteQuadraticDomains.norm_nonzero_of_real_nonzero a b ha
  have he : (((A^2-2*B^2:ℤ):ℚ))=norm (pair a b)*(D:ℚ)^2 := by
    push_cast
    rw [haeq,hbeq,norm_pair]
    ring
  have heval := norm_three_int_value A B hA hB
  rw [he,padicValRat.mul hq (pow_ne_zero _ (by exact_mod_cast hd)),padicValRat.pow] at heval
  rw [Nat.cast_min,hvA,hvB,min_add_add_right] at heval
  norm_num at heval
  rw [norm_pair]
  linarith only [heval]

/-- Exact rational valuation from a displayed prime-power factor and units. -/
theorem rational_scaled_value (p : ℕ) [hp : Fact p.Prime] (k : ℤ) (a b : ℤ)
    (ha : ¬(p:ℤ)∣a) (hb : ¬(p:ℤ)∣b) :
    padicValRat p ((p:ℚ)^k*((a:ℚ)/(b:ℚ)))=k := by
  have hp0 : (p:ℚ)≠0 := by exact_mod_cast hp.out.ne_zero
  have ha0 : a≠0 := fun h => ha (h ▸ dvd_zero _)
  have hb0 : b≠0 := fun h => hb (h ▸ dvd_zero _)
  have hv : padicValRat p (p:ℚ)=1 := padicValRat.self hp.out.one_lt
  rw [padicValRat.mul (zpow_ne_zero _ hp0)
      (div_ne_zero (by exact_mod_cast ha0) (by exact_mod_cast hb0)),
    padicValRat.zpow,hv,rational_unit_value p a b ha hb]
  ring

end AnchorNorm318
