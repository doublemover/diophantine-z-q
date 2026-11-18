module
public import ActualFieldRamificationSupport318
public import ContactRadical318
public import CMDiscriminant318
public section
noncomputable section
namespace CMFieldContactSupport318
open ContactRadical318 ActualFieldRamificationSupport318 Finset

theorem supports_disjoint (u v : ℤ) : Disjoint badPrimes (contactPrimes u v) := by
  apply Finset.disjoint_left.mpr
  intro p hb hc
  obtain ⟨j,_,hn,_⟩ := (mem_contactPrimes u v p).mp hc
  exact hn hb

theorem support_pos (u v : ℤ) : ∀ p∈badPrimes ∪ contactPrimes u v,1≤p := by
  intro p hp
  rcases Finset.mem_union.mp hp with hb|hc
  · by_contra hn
    have he : p=0 := by omega
    subst p
    norm_num [badPrimes] at hb
  · exact (member_prime u v p hc).one_lt.le

/-- The actual field discriminants supply the exact integer and numerical
support fields for CMInputs. Requires local unramifiedness of F away from the
actual five-form set; construction of F and proof of that local fact are not
hidden in this statement. -/
theorem inputs (u v : ℤ) (K F : Type*) [Field K] [NumberField K] [Field F]
    [NumberField F] [Algebra K F]
    (hr : UnramifiedOutside F (badPrimes ∪ contactPrimes u v)) :
    (NumberField.discr F).natAbs ≠ 0 ∧
    (∀ p : ℕ,p.Prime → p∣(NumberField.discr K).natAbs → p∣(NumberField.discr F).natAbs) ∧
    CMDiscriminant318.radical (NumberField.discr F).natAbs ≤ badProduct*radical u v := by
  refine ⟨Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero F),
    fun p _ => subfield_prime K F p,?_⟩
  have h := radical_le F hr (support_pos u v)
  rw [Finset.prod_union (supports_disjoint u v)] at h
  exact h

theorem quadratic_bound (u v : ℤ) (K F : Type*) [Field K] [NumberField K] [Field F]
    [NumberField F] [Algebra K F] (hf : Int.IsFundamentalDiscr (NumberField.discr K))
    (hr : UnramifiedOutside F (badPrimes ∪ contactPrimes u v)) :
    (NumberField.discr K).natAbs≤4*(badProduct*radical u v) := by
  obtain ⟨hn,hs,hr'⟩ := inputs u v K F hr
  exact (CMDiscriminant318.fundamental_discriminant_bound _ _ hf hn hs).trans
    (Nat.mul_le_mul_left _ hr')

end CMFieldContactSupport318
