module
public import SelectedVariableDenominatorUnit318
public section
noncomputable section
namespace FixedSelectedPrimeBound318
open ValuativeOrbitBounds318 ConcretePadic318
open ClearedContactForms318 MergedContactPrimePattern318 ContactPatternSupport318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

/-- All fixed excluded rational numerators and denominators are bounded
before prime selection; the variable w is deliberately absent. -/
@[expose] def bound : ℕ := 76176+C.denominator+
  ∑ j : Fin 3, ((ThreeDetectorArithmetic318.scales labels j).num.natAbs+
    (ThreeDetectorArithmetic318.scales labels j).den)

lemma scale_bounds (j : Fin 3) :
    (ThreeDetectorArithmetic318.scales labels j).num.natAbs≤bound C ∧
    (ThreeDetectorArithmetic318.scales labels j).den≤bound C := by
  have he := Finset.single_le_sum (fun k (_ : k∈(Finset.univ:Finset (Fin 3))) =>
    Nat.zero_le ((ThreeDetectorArithmetic318.scales labels k).num.natAbs+
      (ThreeDetectorArithmetic318.scales labels k).den)) (Finset.mem_univ j)
  unfold bound
  omega

lemma int_unit (p : ℕ) [Fact p.Prime] (n : ℤ) (hn : n≠0) (hnp : n.natAbs<p) :
    rationalPlace p (n:ℚ)=0 := by
  have hnot : ¬p∣n.natAbs := by
    intro hd
    have he := Nat.le_of_dvd (Int.natAbs_pos.mpr hn) hd
    omega
  have he := rational_nat_unit p n.natAbs hnot
  by_cases hsign : 0≤n
  · have hid : (n:ℚ)=(n.natAbs:ℚ) := by
      exact_mod_cast ((Int.natCast_natAbs n).trans (abs_of_nonneg hsign)).symm
    rw [hid]
    exact he
  · have hid : (n:ℚ)= -(n.natAbs:ℚ) := by
      have hh : (n.natAbs:ℤ)= -n := by rw [Int.natCast_natAbs,abs_of_neg (by omega)]
      exact_mod_cast (show n= -(n.natAbs:ℤ) by omega)
    rw [hid,(rationalPlace p).map_neg]
    exact he

lemma rational_unit (p : ℕ) [Fact p.Prime] (q : ℚ) (hq : q≠0)
    (hnum : q.num.natAbs<p) (hden : q.den<p) : rationalPlace p q=0 := by
  have hn : q.num≠0 := by
    intro he
    have hh := Rat.num_div_den q
    rw [he,Int.cast_zero,zero_div] at hh
    exact hq hh.symm
  have hnu := int_unit p q.num hn hnum
  have hdu := rational_nat_unit p q.den (by
    intro hd
    have he := Nat.le_of_dvd q.den_pos hd
    omega)
  conv_lhs => rw [←Rat.num_div_den q]
  rw [(rationalPlace p).map_div,hnu,hdu,sub_self]

/-- The former local-unit avoidance family is now produced from one fixed
prime-size bound and the original five-prime pattern, at all15 positions. -/
theorem avoidance (hn : ∀ j, labels j≠0) (u w : ℤ) (hp : Values C u w)
    (hlarge : ∀ j : Fin 3, ∀ i : Fin 5, bound C<(row C u w j i).natAbs) :
    SelectedOppositeGood318.Avoidance C u w hp := by
  intro j i
  dsimp only
  let p := (row C u w j i).natAbs
  letI : Fact p.Prime := ⟨row_prime C u w hp j i⟩
  have hb := hlarge j i
  have hlarge' : 76176<p := by dsimp [bound] at hb; omega
  have hD : C.denominator<p := by dsimp [bound] at hb; omega
  have hc : ThreeDetectorArithmetic318.scales labels j≠0 := by
    rw [scales_eq]
    exact ContactPrimeForms318.scaleRoot_ne labels hn j
  have hcunit := rational_unit p _ hc
    (lt_of_le_of_lt (scale_bounds C j).1 hb) (lt_of_le_of_lt (scale_bounds C j).2 hb)
  have hdunit : rationalPlace p (C.denominator:ℚ)=0 := rational_nat_unit p C.denominator (by
    intro hd
    exact (not_le_of_gt hD) (Nat.le_of_dvd C.positive hd))
  refine ⟨hlarge',hcunit,?_⟩
  rw [denominator,(rationalPlace p).map_mul,hdunit,
    SelectedVariableDenominatorUnit318.variable_unit C hn u w hp j i,zero_add]

end FixedSelectedPrimeBound318
