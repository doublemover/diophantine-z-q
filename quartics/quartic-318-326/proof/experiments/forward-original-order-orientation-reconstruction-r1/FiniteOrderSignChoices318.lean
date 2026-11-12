module
public import ActualQuarterCoverageObstruction318
public section
noncomputable section
namespace FiniteOrderSignChoices318
variable {ι : Type*} [Fintype ι]
@[expose] def left (a b : ι → ℕ) (s : ι → Bool) (i : ι) : ℕ := if s i then b i else a i
@[expose] def right (a b : ι → ℕ) (s : ι → Bool) (i : ι) : ℕ := if s i then a i else b i
@[expose] def flip (s : ι → Bool) : ι → Bool := fun i => !(s i)
@[expose] def leftLCM (a b : ι → ℕ) (s : ι → Bool) : ℕ := Finset.univ.lcm (left a b s)
@[expose] def rightLCM (a b : ι → ℕ) (s : ι → Bool) : ℕ := Finset.univ.lcm (right a b s)
lemma left_dvd (a b : ι → ℕ) (s : ι → Bool) (i : ι) : left a b s i∣leftLCM a b s :=
  Finset.dvd_lcm (Finset.mem_univ i)
lemma right_dvd (a b : ι → ℕ) (s : ι → Bool) (i : ι) : right a b s i∣rightLCM a b s :=
  Finset.dvd_lcm (Finset.mem_univ i)
/-- Known divisibility at a chosen side forces the SAME side if the opposite is excluded. -/
lemma forced_same (a b : ι → ℕ) (q : ℕ) (s t : ι → Bool) (i : ι)
    (ht : q∣left a b t i) (hs : ¬q∣right a b s i) : s i=t i := by
  cases he : s i <;> cases ht' : t i
  · rfl
  · exact (hs (by simpa only [left,right,he,ht',Bool.false_eq_true,if_false,if_true] using ht)).elim
  · exact (hs (by simpa only [left,right,he,ht',Bool.false_eq_true,if_false,if_true] using ht)).elim
  · rfl
lemma forced_flip (a b : ι → ℕ) (q : ℕ) (s t : ι → Bool) (i : ι)
    (ht : q∣left a b t i) (hs : ¬q∣left a b s i) : s i=flip t i := by
  cases he : s i <;> cases ht' : t i
  · exact (hs (by simpa only [left,he,ht'] using ht)).elim
  · simp only [flip,ht']
  · simp only [flip,ht']
  · exact (hs (by simpa only [left,he,ht'] using ht)).elim
/-- All compatible orientations are a fixed known-divisor assignment or its global flip.
Neither assignment is asserted compatible; common divisors at both sides may obstruct both. -/
theorem two_choices (a b : ι → ℕ) (q : ℕ) (hq : q.Prime) (t : ι → Bool)
    (ht : ∀ i,q∣left a b t i) (s : ι → Bool)
    (hc : Nat.Coprime (leftLCM a b s) (rightLCM a b s)) : s=t ∨ s=flip t := by
  by_cases hleft : q∣leftLCM a b s
  · have hright : ¬q∣rightLCM a b s := by
      intro hd
      have hg:=Nat.dvd_gcd hleft hd
      rw [hc.gcd_eq_one] at hg
      exact hq.not_dvd_one hg
    left
    funext i
    exact forced_same a b q s t i (ht i) (fun hd => hright (hd.trans (right_dvd a b s i)))
  · right
    funext i
    exact forced_flip a b q s t i (ht i) (fun hd => hleft (hd.trans (left_dvd a b s i)))
end FiniteOrderSignChoices318
