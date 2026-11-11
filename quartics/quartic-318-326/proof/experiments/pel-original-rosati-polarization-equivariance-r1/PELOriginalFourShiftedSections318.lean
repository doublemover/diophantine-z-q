module
public import PELOriginalBalancedPowerSections318
public import PELOriginalWholeSectionSpanning318
public section
noncomputable section
namespace PELOriginalFourShiftedSections318
open QuaternionicRealPeriod318 PELOriginalHermitianForm318 PELOriginalPolarizationAutomorphy318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318 PELOriginalPowerSectionDescent318
open PELOriginalBalancedPowerSections318 PELOriginalWholeSectionSpanning318
variable (τ : ℂ) (hτ : 0 < τ.im)

/-- Four shifted ORIGINAL factors balance when their actual vector
shifts sum to zero. The full exponent, including semicharacter, is used. -/
lemma factor_four (l : L τ hτ) (z a b c d : ComplexVectors) (hs : a+b+c+d=0) :
    factor τ hτ l (z+a)*factor τ hτ l (z+b)*factor τ hτ l (z+c)*factor τ hτ l (z+d)=
      factor τ hτ l z^4 := by
  have hh : form τ hτ a l.val+form τ hτ b l.val+form τ hτ c l.val+form τ hτ d l.val=0 := by
    simpa only [map_add,map_zero] using congrArg (PELOriginalHermitianForm318.linear τ hτ l.val) hs
  simp only [factor,←Complex.exp_add,←Complex.exp_nat_mul]
  congr 1
  simp only [exponent,form_add_left]
  linear_combination (Complex.pi : ℂ)*hh

variable (N : ℕ) [NeZero N]
@[expose] def four (i : Fin 4 → Label N) (a : Fin 4 → ComplexVectors)
    (z : ComplexVectors) : ℂ :=
  value τ hτ N (i 0) (z+a 0)*value τ hτ N (i 1) (z+a 1)*
    value τ hτ N (i 2) (z+a 2)*value τ hτ N (i 3) (z+a 3)
lemma entire (i : Fin 4 → Label N) (a : Fin 4 → ComplexVectors) :
    Differentiable ℂ (four τ hτ N i a) :=
  ((((holomorphic τ hτ N (i 0)).comp (differentiable_id.add_const (a 0))).mul
    ((holomorphic τ hτ N (i 1)).comp (differentiable_id.add_const (a 1)))).mul
    ((holomorphic τ hτ N (i 2)).comp (differentiable_id.add_const (a 2)))).mul
    ((holomorphic τ hτ N (i 3)).comp (differentiable_id.add_const (a 3)))
lemma lattice (i : Fin 4 → Label N) (a : Fin 4 → ComplexVectors)
    (hs : a 0+a 1+a 2+a 3=0) (l : L τ hτ) (z : ComplexVectors) :
    four τ hτ N i a (z+l.val)=factor τ hτ l z^(4*N)*four τ hτ N i a z := by
  have h (t : Fin 4) : z+l.val+a t=(z+a t)+l.val := by abel
  simp only [four,h,original_automorphy]
  calc
    _ = (factor τ hτ l (z+a 0)*factor τ hτ l (z+a 1)*
        factor τ hτ l (z+a 2)*factor τ hτ l (z+a 3))^N*four τ hτ N i a z := by
      simp only [mul_pow,four]; ring
    _ = _ := by rw [factor_four τ hτ l z _ _ _ _ hs,←pow_mul]
@[expose] def automorphic (i : Fin 4 → Label N) (a : Fin 4 → ComplexVectors)
    (hs : a 0+a 1+a 2+a 3=0) (c : ℂ) : OriginalAutomorphic τ hτ (4*N) where
  value z := c*four τ hτ N i a z
  entire := differentiable_const.mul (entire τ hτ N i a)
  lattice_rule l z := by rw [lattice τ hτ N i a hs]; ring

/-- Actual whole H0 spanning for each four-shift slice, retaining any
constant factors from the other variables. -/
lemma span [NeZero (4*N)] (i : Fin 4 → Label N) (a : Fin 4 → ComplexVectors)
    (hs : a 0+a 1+a 2+a 3=0) (c : ℂ) :
    ∃ C : Label (4*N) → ℂ,∀ z,c*four τ hτ N i a z=
      ∑ k,C k*value τ hτ (4*N) k z := by
  let f := automorphic τ hτ N i a hs c
  refine ⟨coordinates τ hτ (4*N) (descend τ hτ (4*N) f),?_⟩
  intro z
  have he := original_lift_expansion τ hτ (4*N) (descend τ hτ (4*N) f) z
  rw [lift_descend] at he
  exact he
end PELOriginalFourShiftedSections318
