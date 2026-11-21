module
public import CTActualSplitIsogenyOrthogonal318
import all CTActualFiniteIsogenyLinear318
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
public section
noncomputable section

namespace CTActualRetainedLocalOrthogonality318

open CTActualRetainedScalarPair318 CTActualFiniteIsogenyLinear318
open CTActualPacketIsogenyOrthogonal318 CTActualSplitIsogenyOrthogonal318
open ActualNaturalAllPlacesFinite318 OriginalCasselsNaturalPrimeValuation318
open LinearMap.BilinForm
open scoped BigOperators

local instance : DecidableEq ℝ := Classical.decEq _
local instance (p : ℕ) [Fact p.Prime] : DecidableEq (ℚ_[p]) := Classical.decEq _
local instance {n : ℕ} (i : Support n) : Fact i.val.Prime :=
  ⟨Nat.prime_of_mem_primeFactors i.property⟩

theorem actual_prime_complement (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) (p : ℕ) [Fact p.Prime] (hm : p∈(6*n).primeFactors) :
    (localPrimeForm p).orthogonal (localPlane ℚ_[p] .forward (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne'))=
      localPlane ℚ_[p] .reverse (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne') := by
  by_cases h2 : p=2
  · subst p
    rw [localPrimeForm_two]
    exact dyadic_complement n hn hr
  rw [localPrimeForm_odd p h2]
  by_cases h3 : p=3
  · subst p
    exact ternary_complement n hn hr
  have hP : p.Prime := Fact.out
  have hp5 := five_le_prime_of_ne_two_three hP h2 h3
  have hnD : p∣n := by
    have ha := (Nat.mem_primeFactors.mp hm).2.1
    rcases hP.dvd_mul.mp ha with h6|hD
    · have h6' : p∣2*3 := h6
      rcases hP.dvd_mul.mp h6' with hb|hc
      · have hp2 := Nat.le_of_dvd (by decide : 0<2) hb
        omega
      · have hp3 := Nat.le_of_dvd (by decide : 0<3) hc
        omega
    · exact hD
  have hnM : p∈n.primeFactors := (Nat.mem_primeFactors_of_ne_zero hn.ne').mpr ⟨hP,hnD⟩
  by_cases hSplit : p%3=1
  · exact split_ramified_complement hp5 h2 hSplit (n:ℚ_[p]) (Nat.cast_ne_zero.mpr hn.ne')
      (squarefree_support_valuation_one n p hn hs hnM)
  · exact inert_ramified_complement n hn hs hr p hnM hSplit

/-- The full product of actual forward images and the full product of
actual reverse images are opposite orthogonals for the same retained form. -/
theorem retained_local_complement (n : ℕ) (hn : 0<n) (hs : Squarefree n)
    (hr : (n:ZMod 12)=11) :
    (retainedForm n).orthogonal (localProduct .forward n hn)=localProduct .reverse n hn := by
  have h∞ := real_complement (n:ℝ) (Nat.cast_ne_zero.mpr hn.ne')
  have hp (i : Support n) := actual_prime_complement n hn hs hr i.val i.property
  ext z
  constructor
  · intro hz
    change z.1 ∈ realPlane .reverse n hn ∧ ∀ i, z.2 i ∈ padicPlane .reverse n hn i
    refine ⟨?_,fun i => ?_⟩
    · change z.1 ∈ localPlane ℝ .reverse (n:ℝ) (Nat.cast_ne_zero.mpr hn.ne')
      rw [←h∞]
      apply mem_orthogonal_iff.mpr
      intro y hy
      have hY : ((y,0):RetainedSpace n) ∈ localProduct .forward n hn :=
        ⟨hy,fun i => (padicPlane .forward n hn i).zero_mem⟩
      have he := (mem_orthogonal_iff.mp hz) ((y,0):RetainedSpace n) hY
      simpa only [retainedForm_apply,map_zero,LinearMap.zero_apply,Pi.zero_apply,
        Finset.sum_const_zero,add_zero] using he
    · change z.2 i ∈ localPlane ℚ_[i.val] .reverse (n:ℚ_[i.val]) (Nat.cast_ne_zero.mpr hn.ne')
      rw [←hp i]
      apply mem_orthogonal_iff.mpr
      intro y hy
      let w : (j : Support n) → ScalarBits ℚ_[j.val] := Pi.single i y
      have hY : ((0,w):RetainedSpace n) ∈ localProduct .forward n hn := by
        refine ⟨(realPlane .forward n hn).zero_mem,fun j => ?_⟩
        by_cases h : j=i
        · subst j
          simpa only [w,Pi.single_eq_same] using hy
        · simpa only [w,Pi.single_eq_of_ne h] using (padicPlane .forward n hn j).zero_mem
      have he := (mem_orthogonal_iff.mp hz) ((0,w):RetainedSpace n) hY
      have hSum : (∑ j : Support n,localPrimeForm j.val (w j) (z.2 j))=
          localPrimeForm i.val y (z.2 i) := by
        rw [Finset.sum_eq_single i]
        · rw [show w i=y by simp [w]]
        · intro j _ hji
          rw [show w j=0 by simp [w,hji],map_zero,LinearMap.zero_apply]
        · simp
      simpa only [retainedForm_apply,map_zero,LinearMap.zero_apply,zero_add,hSum] using he
  · intro hz
    change z.1 ∈ realPlane .reverse n hn ∧ ∀ i, z.2 i ∈ padicPlane .reverse n hn i at hz
    apply mem_orthogonal_iff.mpr
    intro y hy
    change y.1 ∈ realPlane .forward n hn ∧ ∀ i, y.2 i ∈ padicPlane .forward n hn i at hy
    have hR : realForm y.1 z.1=0 := by
      have hz' : z.1 ∈ realForm.orthogonal (realPlane .forward n hn) := by
        change z.1 ∈ realForm.orthogonal (localPlane ℝ .forward (n:ℝ) (Nat.cast_ne_zero.mpr hn.ne'))
        rw [h∞]
        exact hz.1
      exact mem_orthogonal_iff.mp hz' y.1 hy.1
    have hP (i : Support n) : localPrimeForm i.val (y.2 i) (z.2 i)=0 := by
      have hz' : z.2 i ∈ (localPrimeForm i.val).orthogonal (padicPlane .forward n hn i) := by
        change z.2 i ∈ (localPrimeForm i.val).orthogonal
          (localPlane ℚ_[i.val] .forward (n:ℚ_[i.val]) (Nat.cast_ne_zero.mpr hn.ne'))
        rw [hp i]
        exact hz.2 i
      exact mem_orthogonal_iff.mp hz' (y.2 i) (hy.2 i)
    rw [retainedForm_apply,hR]
    simp only [hP,Finset.sum_const_zero,add_zero]

end CTActualRetainedLocalOrthogonality318

#print axioms CTActualRetainedLocalOrthogonality318.retained_local_complement
