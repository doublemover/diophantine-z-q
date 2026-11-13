module
public import ActualTwoDescentActualAllPlacesBound318
public section
noncomputable section
namespace ActualTwoDescentActualCubeIndependence318
set_option maxHeartbeats 16000000

open ActualTwoDescentSquareClassQuotient318 ActualTwoDescentEightClassCube318
open ActualTwoDescentTorsionKummerValues318 ActualTwoDescentPrimeMonomials318
open ActualTwoDescentLiteralEightClasses318 ActualTwoDescentZeroSumCompletion318
open scoped BigOperators
variable {U : Type*} [Fintype U] [DecidableEq U]

lemma actual_negative_class_ne_one (n : ℚ) (hn : 0 < n) : classOf (-n) (neg_ne_zero.mpr hn.ne') ≠ 1 := by
  intro he
  rw [←class_of_one] at he
  obtain ⟨s,hs,h⟩ := (class_of_eq_iff _ _ _ _).mp he
  nlinarith [sq_nonneg s]

lemma actual_bit_power_injective {G : Type*} [Group G] (g : G) (hg : g ≠ 1) :
    Function.Injective (fun e : ZMod 2 => g^e.val) := by
  intro e f h
  fin_cases e <;> fin_cases f <;> simp_all

/-- Independence of the ACTUAL rational squareclasses follows from the literal
prime valuations and one beta0 and one beta1 support coordinate. -/
theorem actual_cube_independent (p : Option U → ℕ) [∀ i, Fact (p i).Prime]
    (hd : Function.Injective p) (beta : Option U → ZMod 2)
    (i0 i1 : Option U) (h0 : beta i0=0) (h1 : beta i1=1) :
    Function.Injective (cubeClass ((∏ i, p i : ℕ) : ℚ) (monomial p beta : ℚ)
      (Nat.cast_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr (fun i _ => (Fact.out : (p i).Prime).ne_zero)))
      (Nat.cast_ne_zero.mpr (monomial_pos p beta).ne')) := by
  let n : ℚ := ∏ i, p i
  let b : ℚ := monomial p beta
  have hn : 0 < n := by exact_mod_cast Finset.prod_pos (fun i _ => (Fact.out : (p i).Prime).pos)
  have hb : b ≠ 0 := Nat.cast_ne_zero.mpr (monomial_pos p beta).ne'
  rintro ⟨ε,c,e⟩ ⟨δ,c',e'⟩ H
  have hsecond := congrArg Prod.snd H
  change classOf (-n) _ ^ ε.val*(1 : SquareClass ℚ)^c.val*1^e.val=
    classOf (-n) _ ^ δ.val*1^c'.val*1^e'.val at hsecond
  simp only [one_pow,mul_one] at hsecond
  have hεδ : ε=δ := actual_bit_power_injective _ (actual_negative_class_ne_one n hn) hsecond
  subst δ
  have hfirst := congrArg Prod.fst H
  change classOf (3 : ℚ) _ ^ ε.val*classOf n hn.ne' ^ c.val*classOf b hb ^ e.val=
    classOf (3 : ℚ) _ ^ ε.val*classOf n hn.ne' ^ c'.val*classOf b hb ^ e'.val at hfirst
  have hce : classOf n hn.ne' ^ c.val*classOf b hb ^ e.val=
      classOf n hn.ne' ^ c'.val*classOf b hb ^ e'.val := by
    apply mul_left_cancel (a:=classOf (3 : ℚ) (by norm_num)^ε.val)
    simpa only [mul_assoc] using hfirst
  have hmono (c e : ZMod 2) : classOf (monomial p (c • ones (Option U)+e • beta) : ℚ)
      (Nat.cast_ne_zero.mpr (monomial_pos p _).ne')=
      classOf n hn.ne' ^ c.val*classOf b hb ^ e.val := by
    obtain ⟨t,ht,he⟩ := actual_four_monomial_classes p beta c e
    rw [←class_of_pow,←class_of_pow,←class_of_mul]
    exact (class_of_eq_iff _ _ _ _).mpr ⟨t,ht,he⟩
  have hclasses := (hmono c e).trans (hce.trans (hmono c' e').symm)
  obtain ⟨r,hr,he⟩ := (class_of_eq_iff _ _ _ _).mp hclasses
  have hv := actual_monomial_squareclass_injective p hd _ _ r hr he
  have hc := congrFun hv i0
  change c*1+e*beta i0=c'*1+e'*beta i0 at hc
  simp only [h0,mul_zero,add_zero,mul_one] at hc
  subst c'
  have heq := congrFun hv i1
  change c*1+e*beta i1=c*1+e'*beta i1 at heq
  simp only [h1,mul_one,add_left_cancel_iff] at heq
  subst e'
  rfl

end ActualTwoDescentActualCubeIndependence318
