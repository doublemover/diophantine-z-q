module
public import OriginalAffinePrimeSupport318
public section
noncomputable section
namespace OriginalQuadraticIntegerFibers318
open scoped BigOperators
open IntegerResidueBoxCount318
set_option maxHeartbeats 4500000

@[expose] def roots {F : Type*} [Field F] [Fintype F] [DecidableEq F] (a b c : F) : Finset F :=
  Finset.univ.filter (fun x => a*x^2+b*x+c=0)

/-- Nonmonic quadratic root count in EVERY finite field, including
characteristic2. No completion-of-square division by2 is used. -/
lemma roots_card {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a b c : F) (ha : a≠0) : (roots a b c).card≤2 := by
  classical
  by_cases hh : (roots a b c).Nonempty
  · obtain ⟨y,hy⟩ := hh
    have hy0 : a*y^2+b*y+c=0 := (Finset.mem_filter.mp hy).2
    have hs : roots a b c⊆{y,-b/a-y} := by
      intro x hx
      have hx0 : a*x^2+b*x+c=0 := (Finset.mem_filter.mp hx).2
      have hf : (x-y)*(a*(x+y)+b)=0 := by linear_combination hx0-hy0
      rcases mul_eq_zero.mp hf with hxy|hl
      · exact Finset.mem_insert.mpr (Or.inl (sub_eq_zero.mp hxy))
      · have he : x+y=-b/a := (eq_div_iff ha).mpr (by linear_combination hl)
        have hx' : x=-b/a-y := by linear_combination he
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr hx'))
    exact (Finset.card_le_card hs).trans (by simp)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hh]
    simp

@[expose] def IntegerRoots (B p : ℕ) (a b c : ℤ) :=
  {h : Interval B // (p:ℤ)∣a*h.1^2+b*h.1+c}

/-- Actual integer interval roots, retaining the exact residue-fiber
boundary term rather than silently identifying integers with residues. -/
theorem integer_root_count (B p : ℕ) [Fact p.Prime] (a b c : ℤ) (ha : ¬(p:ℤ)∣a) :
    Nat.card (IntegerRoots B p a b c)≤2*(2*B/p+1) := by
  classical
  let Z := roots (a:ZMod p) (b:ZMod p) (c:ZMod p)
  let Target := Σ r : ↥Z, ResidueBox B p (r.1.val:ℤ)
  let f : IntegerRoots B p a b c → Target := fun h =>
    ⟨⟨(h.1.1:ZMod p),by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have hh := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h.2
      simpa only [Int.cast_add,Int.cast_mul,Int.cast_pow] using hh⟩,
      ⟨h.1,OriginalAnisotropicResidueFibers318.self_residue_divides p h.1.1⟩⟩
  have hf : Function.Injective f := by
    intro h k he
    exact Subtype.ext (congrArg (fun z : Target => z.2.1) he)
  have hc := Nat.card_le_card_of_injective f hf
  have hZ : Z.card≤2 := roots_card _ _ _ (fun h => ha ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h))
  have ht : Nat.card Target≤Z.card*(2*B/p+1) := by
    rw [Nat.card_eq_fintype_card,Fintype.card_sigma]
    calc
      _ = ∑ r : ↥Z, Nat.card (ResidueBox B p (r.1.val:ℤ)) := by simp only [Nat.card_eq_fintype_card]
      _ ≤ ∑ _r : ↥Z, 2*B/p+1 := Finset.sum_le_sum (fun r _ =>
        residue_box_card B p (Fact.out : p.Prime).pos _)
      _ = _ := by simp
  exact hc.trans (ht.trans (Nat.mul_le_mul_right _ hZ))

/-- For a prime strictly larger than the FULL interval width, at most
two original integers occur. A comparison to the half-width alone would
be insufficient and is not used. -/
theorem large_prime_root_count (B p : ℕ) [Fact p.Prime] (a b c : ℤ)
    (ha : ¬(p:ℤ)∣a) (hp : 2*B<p) : Nat.card (IntegerRoots B p a b c)≤2 := by
  simpa only [Nat.div_eq_of_lt hp,zero_add,mul_one] using integer_root_count B p a b c ha

end OriginalQuadraticIntegerFibers318
