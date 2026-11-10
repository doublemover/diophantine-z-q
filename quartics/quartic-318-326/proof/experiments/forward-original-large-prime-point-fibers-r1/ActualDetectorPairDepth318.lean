module
public import ActualDetectorTrace318
public section
noncomputable section
namespace ActualDetectorPairDepth318
open CircuitReplay ConcreteG8Domain ActualDetectorFold318 NormChainCompleteness
open scoped QuadraticAlgebra
set_option maxHeartbeats 1000000

@[expose] def NearPair (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (x : K) : Prop :=
  (k:WithTop ℤ)<v (x.re-1) ∧ (k:WithTop ℤ)<v x.im

lemma add_deep (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (x y : ℚ)
    (hx : (k:WithTop ℤ)<v x) (hy : (k:WithTop ℤ)<v y) :
    (k:WithTop ℤ)<v (x+y) := lt_of_lt_of_le (lt_min hx hy) (v.map_add x y)

lemma mul_deep (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (x y : ℚ)
    (hx : (k:WithTop ℤ)<v x) (hy : 0≤v y) : (k:WithTop ℤ)<v (x*y) := by
  rw [v.map_mul]
  exact lt_of_lt_of_le hx (le_add_of_nonneg_right hy)

lemma square_deep (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (hk : 0≤k)
    (x : ℚ) (hx : (k:WithTop ℤ)<v x) : (k:WithTop ℤ)<v (x^2) := by
  rw [pow_two]
  exact mul_deep v k x x hx (le_trans (by exact_mod_cast hk) (le_of_lt hx))

/-- Squaring the actual quadratic pair preserves any nonnegative precision.
This includes p=2; no split embedding or odd-residue premise occurs. -/
lemma square_pair (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (hk : 0≤k)
    (h2 : 0≤v (2:ℚ)) (x : K) (hx : NearPair v k x) : NearPair v k (x^2) := by
  obtain ⟨ha,hb⟩ := hx
  have ha0 : v x.re=0 := near_one_value v x.re (lt_of_le_of_lt (by exact_mod_cast hk) ha)
  have hasum : 0≤v (x.re+1) := by simpa only [ha0,v.map_one] using v.map_add x.re 1
  have hsq : (k:WithTop ℤ)<v (x.re^2-1) := by
    rw [show x.re^2-1=(x.re-1)*(x.re+1) by ring]
    exact mul_deep v k _ _ ha hasum
  have himsq : (k:WithTop ℤ)<v (2*x.im^2) := by
    rw [mul_comm (2:ℚ)]
    exact mul_deep v k _ _ (square_deep v k hk _ hb) h2
  have hreal := add_deep v k _ _ hsq himsq
  have hcoef : 0≤v (2*x.re) := by rw [v.map_mul,ha0,add_zero]; exact h2
  have himag := mul_deep v k _ _ hb hcoef
  constructor
  · convert hreal using 1 <;> simp [pow_two] <;> ring
  · convert himag using 1 <;> simp [pow_two] <;> ring

lemma step_pair (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (hk : 0≤k)
    (h2 : 0≤v (2:ℚ)) (x y : K) (hx : NearPair v k x)
    (hy : (k:WithTop ℤ)<v y.re ∧ (k:WithTop ℤ)<v y.im) : NearPair v k (x^2+y) := by
  have hs := square_pair v k hk h2 x hx
  constructor
  · have hh := add_deep v k _ _ hs.1 hy.1
    convert hh using 1 <;> simp only [QuadraticAlgebra.re_add] <;> ring
  · simpa only [QuadraticAlgebra.im_add] using add_deep v k _ _ hs.2 hy.2

lemma fold_pair (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (hk : 0≤k)
    (h2 : 0≤v (2:ℚ)) (xs : List (K×K)) (x : K) (hx : NearPair v k x)
    (h : ∀ a∈xs, (k:WithTop ℤ)<v (a.1*a.2).re ∧
      (k:WithTop ℤ)<v (a.1*a.2).im) :
    NearPair v k (xs.foldl (fun z a => z^2+a.1*a.2) x) := by
  induction xs generalizing x with
  | nil => simpa using hx
  | cons a xs ih =>
    exact ih _ (step_pair v k hk h2 x _ hx (h a (by simp)))
      (fun b hb => h b (List.mem_cons_of_mem _ hb))

/-- Componentwise depths at all sixteen literal weighted leaves propagate
through the actual source chain, at every rational prime including2. -/
theorem actual_pair (v : AddValuation ℚ (WithTop ℤ)) (k : ℤ) (hk : 0≤k)
    (h2 : 0≤v (2:ℚ)) (w : Assignment)
    (h : ∀ a∈leaves w, (k:WithTop ℤ)<v (a.1*a.2).re ∧
      (k:WithTop ℤ)<v (a.1*a.2).im) : NearPair v k (chain w) := by
  rw [←fold_actual]
  apply fold_pair v k hk h2 _ 1 _ h
  constructor <;> simp [NearPair]

/-- Near(1,0) makes the rational norm and the real coefficient units, so
the trace quotient has exactly the negative valuation of2, even at2. -/
theorem quotient_value (p : ℕ) [Fact p.Prime] (w : Assignment)
    (h : ∀ a∈leaves w,
      0<ConcretePadic318.rationalPlace p (a.1*a.2).re ∧
      0<ConcretePadic318.rationalPlace p (a.1*a.2).im) :
    ContactChainWitness318.value187 w≠0 ∧
    padicValRat p
      (((ContactChainWitness318.value187 w)^2-2*(ContactChainWitness318.value188 w)^2)/
        (2*ContactChainWitness318.value187 w))= -padicValRat p (2:ℚ) := by
  let v := ConcretePadic318.rationalPlace p
  have h2 : 0≤v (2:ℚ) := by
    dsimp [v]
    rw [ConcretePadic318.rational_value p 2 (by norm_num)]
    have he := padicValRat.of_nat (p:=p) (n:=2)
    rw [show (2:ℚ)=(2:ℕ) by norm_num,he]
    exact_mod_cast (Nat.zero_le (padicValNat p 2))
  have hx := actual_pair v 0 (by norm_num) h2 w h
  let a := ContactChainWitness318.value187 w
  let b := ContactChainWitness318.value188 w
  have ha : 0<v (a-1) := hx.1
  have hb : 0<v b := hx.2
  have hav : v a=0 := near_one_value v a ha
  have ha0 : a≠0 := by
    intro hz
    rw [hz,v.map_zero] at hav
    exact WithTop.top_ne_coe hav
  have hb2 : 0<v (2*b^2) := by
    rw [mul_comm (2:ℚ)]
    exact mul_deep v 0 _ _ (square_deep v 0 (by norm_num) _ hb) h2
  have hnormnear : 0<v (a^2-2*b^2-1) := by
    have he := add_deep v 0 (a^2-1) (-(2*b^2))
      (near_one_square v a ha) (by simpa using hb2)
    convert he using 1 <;> ring
  have hnorm : v (a^2-2*b^2)=0 := near_one_value v _ hnormnear
  have hn0 : a^2-2*b^2≠0 := by
    intro hz
    rw [hz,v.map_zero] at hnorm
    exact WithTop.top_ne_coe hnorm
  have hav' : padicValRat p a=0 := by
    rw [ConcretePadic318.rational_value p a ha0] at hav
    exact_mod_cast hav
  have hnorm' : padicValRat p (a^2-2*b^2)=0 := by
    rw [ConcretePadic318.rational_value p _ hn0] at hnorm
    exact_mod_cast hnorm
  refine ⟨ha0,?_⟩
  change padicValRat p ((a^2-2*b^2)/(2*a))=_
  rw [padicValRat.div hn0 (mul_ne_zero (by norm_num) ha0),
    padicValRat.mul (by norm_num) ha0,hnorm',hav']
  ring

end ActualDetectorPairDepth318
