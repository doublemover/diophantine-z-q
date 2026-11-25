module

public import OriginalFineArithmeticPlaceSwitch318
public import Mathlib.Algebra.Module.Equiv.Basic

@[expose] public section
noncomputable section

namespace OriginalCommonHodgeScalar318

open OriginalFineArithmeticPlaceSwitch318

variable {E : Type*} [Field E]
variable {H₀ C₀ : Type*} [AddCommGroup H₀] [AddCommGroup C₀] [Module E H₀] [Module E C₀]
variable {H C : Lane→Type*}
variable [∀ n,AddCommGroup (H n)] [∀ n,AddCommGroup (C n)]
variable [∀ n,Module E (H n)] [∀ n,Module E (C n)]

/- The caller supplies the actual rational frame \ell^2 on the
full marked Hodge square, and Q on the old canonical square.
Both lower coordinates are derived by composition with the
same pointed family and old relative cotangent comparisons. -/
variable (h₀ : H₀≃ₗ[E]E) (c₀ : C₀≃ₗ[E]E)
variable (hTransport : ∀ n,H n≃ₗ[E]H₀) (cTransport : ∀ n,C n≃ₗ[E]C₀)
variable (globalKS : H₀→ₗ[E]C₀) (lowerKS : ∀ n,H n→ₗ[E]C n)
variable (coherent : ∀ n z,cTransport n (lowerKS n z)=globalKS (hTransport n z))

/-- k is computed once from Ψ_E(\ell²)=kQ on the retained E.
There cannot be a different k at the 3-place or 11-place. -/
def heldScalar : E := c₀ (globalKS (h₀.symm 1))

theorem held_nonzero (h : Function.Injective globalKS) :
    heldScalar h₀ c₀ globalKS≠0 := by
  intro e
  have e' : globalKS (h₀.symm 1)=0 := c₀.injective (by
    simpa only [map_zero] using e)
  have bad : h₀.symm 1=0 := h (by simpa only [map_zero] using e')
  exact one_ne_zero (by
    have q := congrArg h₀ bad
    simpa only [LinearEquiv.apply_symm_apply,map_zero] using q)

theorem common_raw_reads_all (x : H₀) :
    c₀ (globalKS x)=h₀ x*heldScalar h₀ c₀ globalKS := by
  have hx : h₀ x • h₀.symm 1=x := by
    apply h₀.injective
    simp only [map_smul,LinearEquiv.apply_symm_apply,smul_eq_mul,mul_one]
  calc
    _ = c₀ (globalKS (h₀ x • h₀.symm 1)) := by rw [hx]
    _ = _ := by simp only [map_smul,smul_eq_mul,heldScalar]

include coherent in
theorem both_actual_lines_read_one_scalar (n : Lane) (x : H n) :
    c₀ (cTransport n (lowerKS n x))=
      h₀ (hTransport n x)*heldScalar h₀ c₀ globalKS := by
  rw [coherent,common_raw_reads_all]

end OriginalCommonHodgeScalar318
