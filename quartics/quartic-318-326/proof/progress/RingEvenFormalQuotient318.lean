module
public import TameLinearization318
public import Mathlib.RingTheory.PowerSeries.Expand
public section
noncomputable section
namespace RingEvenFormalQuotient318
open PowerSeries
variable {k:Type*} [CommRing k] [IsDomain k]

/-- The actual fixed series for T↦−T have exactly the even coefficients. -/
theorem fixed_iff_odd_coeff_zero (h2:(2:k)≠0) (f:k⟦X⟧) :
    rescale (-1:k) f=f ↔ ∀n:ℕ,Odd n→coeff n f=0 := by
  constructor
  · intro h n hn
    have he:=congrArg (coeff n) h
    rw [coeff_rescale,hn.neg_one_pow] at he
    have hz:(2:k)*coeff n f=0 := by linear_combination -he
    exact (mul_eq_zero.mp hz).resolve_left h2
  · intro h
    ext n
    rw [coeff_rescale]
    rcases Nat.even_or_odd n with hn|hn
    · rw [hn.neg_one_pow,one_mul]
    · rw [h n hn,mul_zero]

/-- Recover coefficients of the actual quotient series in the parameter T². -/
@[expose] def halve (f:k⟦X⟧) : k⟦X⟧ := PowerSeries.mk (fun n=>coeff (2*n) f)

theorem expand_halve (f:k⟦X⟧) (h:∀n:ℕ,Odd n→coeff n f=0) :
    expand 2 (by decide) (halve f)=f := by
  ext n
  by_cases hn:2∣n
  · obtain ⟨m,rfl⟩:=hn
    simp only [coeff_expand_mul,halve,coeff_mk]
  · rw [coeff_expand_of_not_dvd 2 (by decide) _ hn]
    symm
    apply h n
    rcases Nat.even_or_odd n with he|ho
    · exact (hn he.two_dvd).elim
    · exact ho

theorem expand_two_injective : Function.Injective (expand 2 (by decide) (R:=k)) := by
  intro f g h
  ext n
  have he:=congrArg (coeff (2*n)) h
  simpa only [coeff_expand_mul] using he

/-- The fixed subring is exactly the image of the actual substitution T↦T²,
with a unique quotient series. -/
theorem fixed_iff_existsUnique (h2:(2:k)≠0) (f:k⟦X⟧) :
    rescale (-1:k) f=f ↔ ∃!g:k⟦X⟧,expand 2 (by decide) g=f := by
  constructor
  · intro h
    refine ⟨halve f,expand_halve f ((fixed_iff_odd_coeff_zero h2 f).mp h),?_⟩
    intro g hg
    exact expand_two_injective (hg.trans (expand_halve f
      ((fixed_iff_odd_coeff_zero h2 f).mp h)).symm)
  · rintro ⟨g,hg,_⟩
    apply (fixed_iff_odd_coeff_zero h2 f).mpr
    intro n hn
    rw [←hg]
    exact coeff_expand_of_not_dvd 2 (by decide) g (by
      intro hd
      exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr hd))

/-- Actual substitution formulation of the quotient invariant-ring statement. -/
theorem subst_fixed_iff_existsUnique (h2:(2:k)≠0) (f:k⟦X⟧) :
    f.subst (-X)=f ↔ ∃!g:k⟦X⟧,g.subst (X^2)=f := by
  simpa only [rescale_eq_subst,neg_one_smul,expand_apply] using fixed_iff_existsUnique h2 f

/-- The quotient parameter has exact ramification order two. -/
theorem quotient_parameter_order : (X^2:k⟦X⟧).order=2 := order_X_pow 2

/-- Its actual formal derivative has exact order one in residue characteristic
not two, the local coefficient used by the tame double quotient. -/
theorem quotient_derivative_order (h2:(2:k)≠0) :
    (derivative (X^2:k⟦X⟧)).order=1 := by
  apply order_eq_nat.mpr
  constructor
  · simpa [coeff_derivative,coeff_X_pow] using h2
  · intro i hi
    have hi0:i=0 := by omega
    subst i
    simp [coeff_derivative,coeff_X_pow]

end RingEvenFormalQuotient318
