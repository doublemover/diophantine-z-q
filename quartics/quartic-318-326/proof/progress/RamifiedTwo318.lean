module
public import LocalGenerator318
public import Mathlib.NumberTheory.Padics.PadicNumbers
public section
namespace RamifiedTwo318
open ConcreteG8Domain AnchorNorm318
open scoped QuadraticAlgebra
set_option maxHeartbeats 0
noncomputable section

instance two_prime : Fact (Nat.Prime 2) := ⟨by norm_num⟩
@[expose] def rational : AddValuation ℚ (WithTop ℤ) :=
  Padic.addValuation.comap (algebraMap ℚ ℚ_[2])

theorem rational_value (q : ℚ) (hq : q≠0) :
    rational q=(padicValRat 2 q:WithTop ℤ) := by
  change Padic.addValuation (q:ℚ_[2])=_
  rw [Padic.addValuation.apply (by exact_mod_cast hq),Padic.valuation_ratCast]

theorem rational_two : rational 2=1 := by
  rw [rational_value _ (by norm_num)]
  have hv : padicValRat 2 (2:ℚ)=1 := padicValRat.self (by norm_num)
  rw [hv]
  rfl

/-- Norm valuation before bundling its triangle law. It is twice the customary
normalization at the ramified prime, so v(2)=2 and v(sqrt(2))=1. -/
@[expose] def value (x : K) : WithTop ℤ := rational (norm x)

theorem pair_value (a b : ℚ) :
    value (pair a b)=min (2 • rational a) (1+2 • rational b) := by
  by_cases ha : a=0
  · subst a
    simp only [value,norm_pair,zero_pow (by decide : 2≠0),zero_sub,
      AddValuation.map_neg,AddValuation.map_mul,AddValuation.map_pow,
      rational_two,AddValuation.map_zero]
    simp [two_nsmul]
  by_cases hb : b=0
  · subst b
    simp only [value,norm_pair,zero_pow (by decide : 2≠0),mul_zero,sub_zero,
      AddValuation.map_pow,AddValuation.map_zero]
    simp [two_nsmul]
  have hn : norm (pair a b)≠0 := by
    simpa only [norm_pair] using ConcreteQuadraticDomains.norm_nonzero_of_real_nonzero a b ha
  rw [value,rational_value _ hn,norm_two_value a b ha hb,
    rational_value _ ha,rational_value _ hb]
  norm_cast

private theorem doubled_min (a b : WithTop ℤ) :
    2 • min a b=min (2 • a) (2 • b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h,min_eq_left (nsmul_le_nsmul_right h 2)]
  · rw [min_eq_right h,min_eq_right (nsmul_le_nsmul_right h 2)]

theorem value_add (x y : K) : min (value x) (value y)≤value (x+y) := by
  obtain ⟨a,b⟩ := x
  obtain ⟨c,d⟩ := y
  change min (value (pair a b)) (value (pair c d))≤value (pair (a+c) (b+d))
  rw [pair_value,pair_value,pair_value]
  apply le_min
  · have h0 := nsmul_le_nsmul_right (rational.map_add a c) 2
    rw [doubled_min] at h0
    exact le_trans (min_le_min (min_le_left _ _) (min_le_left _ _)) h0
  · have h0 := add_le_add_left (nsmul_le_nsmul_right (rational.map_add b d) 2) (1:WithTop ℤ)
    rw [doubled_min, ←min_add_add_right] at h0
    have h1 : min (1+2 • rational b) (1+2 • rational d)≤1+2 • rational (b+d) := by
      simpa only [add_comm] using h0
    exact le_trans (min_le_min (min_le_right _ _) (min_le_right _ _)) h1

@[expose] def place : AddValuation K (WithTop ℤ) := AddValuation.of value
  (by simp [value,AnchorNorm318.norm])
  (by simp [value,AnchorNorm318.norm])
  value_add
  (by intro x y; simp [value,AnchorNorm318.norm_mul])

theorem place_value (x : K) : place x=value x := rfl

theorem place_norm (x : K) (hx : x≠0) :
    place x=(padicValRat 2 (norm x):WithTop ℤ) :=
  rational_value _ (norm_ne_zero hx)

theorem place_two : place (2:K)=2 := by
  change rational (norm (2:K))=2
  have hn : norm (2:K)=(2:ℚ)^2 := by
    exact QuadraticAlgebra.norm_natCast 2
  rw [hn]
  rw [rational.map_pow,rational_two]
  norm_num

theorem place_i : place i=1 := by
  change value (pair 0 1)=1
  rw [pair_value]
  simp [two_nsmul]

theorem place_D : place D=0 := by
  change rational (norm D)=0
  have hn : norm D=49 := by norm_num [D,i,pair,AnchorNorm318.norm,QuadraticAlgebra.norm_def,pow_succ]
  rw [hn,rational_value _ (by norm_num)]
  have hh : padicValRat 2 (49:ℚ)=0 := by
    simpa using rational_unit_value 2 49 1 (by norm_num) (by norm_num)
  rw [hh]
  rfl

theorem generator_x_value : place LocalGenerator318.xP= -6 := by
  rw [place_norm]
  · rw [LocalGenerator318.two_value_xP]; rfl
  · intro h
    have hh := LocalGenerator318.norm_xP
    rw [h] at hh
    norm_num [AnchorNorm318.norm] at hh

theorem generator_z_value : place LocalGenerator318.zP=3 := by
  rw [place_norm]
  · rw [LocalGenerator318.two_value_zP]; rfl
  · intro h
    have hh := LocalGenerator318.norm_zP
    rw [h] at hh
    norm_num [AnchorNorm318.norm] at hh

end
end RamifiedTwo318
