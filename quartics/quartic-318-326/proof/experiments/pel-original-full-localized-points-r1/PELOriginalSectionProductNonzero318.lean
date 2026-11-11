module
public import PELOriginalSectionMultiplication318
public import EntireSimultaneousNonzero318
public section
noncomputable section
namespace PELOriginalSectionProductNonzero318
open QuaternionicRealPeriod318 PELOriginalSectionMultiplication318
open PELOriginalWholeHZeroDimension318 PELOriginalPowerSectionLift318
open PELOriginalPowerSectionDescent318 PELOriginalPolarizationTransitions318
open PELOriginalPolarizationLineBundle318
variable (τ:ℂ)(hτ:0<τ.im)
/-- A nonzero ACTUAL holomorphic section has a nonzero value in its
produced entire cover representative. This uses genuine section descent,
not an assumption that the section is already a theta expansion. -/
lemma lift_nontrivial(n:ℕ)(s:homogeneous τ hτ n)(hs:s≠0):
    ∃z:ComplexVectors,lift τ hτ n (asSection τ hτ n s) z≠0:=by
  by_contra h
  push_neg at h
  apply hs
  apply Subtype.ext
  funext q
  let a:ComplexVectors:=(core τ hτ).indexAt q
  have he:=descend_lift τ hτ n (asSection τ hτ n s) q
  change lift τ hτ n (asSection τ hτ n s) (chart τ hτ a q)=s.val q at he
  exact he.symm.trans (h _)
/-- Nonzero genuine original sections have nonzero product. The proof
uses the actual affine complex line joining two nonzero entire-lift
witnesses, so it does not assume isolated zeros in complex dimension2. -/
theorem multiply_ne_zero(m n:ℕ)(s:homogeneous τ hτ m)(t:homogeneous τ hτ n)
    (hs:s≠0)(ht:t≠0):multiply τ hτ m n s t≠0:=by
  obtain ⟨z,hz⟩:=EntireSimultaneousNonzero318.differentiable_exists_product_ne_zero
    (lift τ hτ m (asSection τ hτ m s)) (lift τ hτ n (asSection τ hτ n t))
    (entire τ hτ m _) (entire τ hτ n _)
    (lift_nontrivial τ hτ m s hs) (lift_nontrivial τ hτ n t ht)
  intro he
  have hzero:lift τ hτ (m+n) (asSection τ hτ (m+n) (multiply τ hτ m n s t)) z=0:=by
    rw [he]
    simp only [lift,asSection,Submodule.coe_zero,Pi.zero_apply,mul_zero]
  rw [lift_product] at hzero
  exact hz hzero
/-- The SAME original coefficient functions have no zero-divisor pair
when they are genuine homogeneous holomorphic sections. This is not a
claim that the ambient ring of ALL functions is a domain. -/
lemma coefficient_product_ne_zero(m n:ℕ)(s t:Values τ)
    (hs:s∈homogeneous τ hτ m)(ht:t∈homogeneous τ hτ n)(hns:s≠0)(hnt:t≠0):s*t≠0:=by
  have h:=multiply_ne_zero τ hτ m n ⟨s,hs⟩ ⟨t,ht⟩
    (fun hz=>hns (congrArg Subtype.val hz)) (fun hz=>hnt (congrArg Subtype.val hz))
  intro hz
  exact h (Subtype.ext hz)
end PELOriginalSectionProductNonzero318
