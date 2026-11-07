module
public import NormChainExtraction
public section
namespace EvenDeltaValuation

/-- Integer consequences of the three local-valuation cases for delta=v-1.
The curve-to-valuation case split is an explicit hypothesis; the actual valuation construction is not asserted. -/
theorem even_and_positive_case (u delta : ℤ)
    (hnegative : u<0 → delta=2*u)
    (hnonnegative : 0≤u → delta=0 ∨ delta=4*u) :
    Even delta ∧ (0<delta → delta=4*u ∧ 0<u) := by
  by_cases hu : u<0
  · have hd := hnegative hu
    constructor
    · exact ⟨u,by omega⟩
    · intro hp
      omega
  · have hu : 0≤u := by omega
    rcases hnonnegative hu with hd | hd
    · subst delta
      exact ⟨⟨0,by norm_num⟩,by omega⟩
    · constructor
      · exact ⟨2*u,by omega⟩
      · intro hp
        exact ⟨hd,by omega⟩

/-- Even valuation of the right leaf, not existence of a global square root,
is sufficient for the odd/even no-tie argument. -/
theorem unequal_summands (R previous m leafValue : ℤ)
    (hR : Odd R) (hleaf : Even leafValue) :
    2*previous ≠ leafValue-(2*m-1)*R := by
  obtain ⟨leaf,hleaf⟩ := hleaf
  have he : leafValue=2*leaf := by omega
  rw [he]
  exact NormChainExtraction.unequal_summands R previous m leaf hR

/-- The linear-delta weight q1 has valuation -R. Its backward threshold
already forces the +1 reciprocal branch; no squared leaf is needed. -/
theorem linear_branch_positive (R delta : ℤ) (hR : 0<R)
    (hthreshold : 0<2*(delta-R)+R) : 0<delta := by omega

theorem linear_branch_formal (R u delta : ℤ) (hR : 0<R)
    (hthreshold : 0<2*(delta-R)+R)
    (hnegative : u<0 → delta=2*u)
    (hnonnegative : 0≤u → delta=0 ∨ delta=4*u) :
    delta=4*u ∧ 0<u :=
  (even_and_positive_case u delta hnegative hnonnegative).2
    (linear_branch_positive R delta hR hthreshold)
end EvenDeltaValuation
