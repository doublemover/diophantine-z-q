module
public import PELNormalizerReductionAction318
public import Mathlib.FieldTheory.Finite.Basic
public section
noncomputable section
namespace PELNormalizerResidueFrobenius318
open PELOrderReductionThree318 PELReductionResidueField318 PELNormalizerReductionAction318
set_option maxHeartbeats 1000000

/-- The genuine nontrivial automorphism of the same actualF9 residue field. -/
@[expose] def conjugation : Residue ≃+* Residue where
  toFun x := ⟨x.re,-x.im⟩
  invFun x := ⟨x.re,-x.im⟩
  left_inv x := by ext <;> simp
  right_inv x := by ext <;> simp
  map_add' x y := by ext <;> simp <;> ring
  map_mul' x y := by ext <;> simp <;> ring

/-- Frobenius on the actual quadratic residue carrier, with arbitrary
coordinates retained and the native prime-field power identity applied. -/
theorem conjugation_frobenius (x : Residue) : conjugation x=x^3 := by
  have h3 : (3:F3)=0 := by decide
  have hr : x.re^3=x.re := ZMod.pow_card x.re
  have hi : x.im^3=x.im := ZMod.pow_card x.im
  ext <;> norm_num [conjugation,pow_succ,pow_two]
  · linear_combination -hr - (2*x.re*x.im^2)*h3
  · linear_combination -2*hi - (x.im+x.re^2*x.im)*h3

theorem conjugation_nontrivial : conjugation (QuadraticAlgebra.omega:Residue)≠
    (QuadraticAlgebra.omega:Residue) := by
  intro h
  have hh := congrArg QuadraticAlgebra.im h
  change -(1:F3)=1 at hh
  exact (by decide : -(1:F3)≠1) hh

/-- Only the actual norm3 representative acts by Frobenius onF9. The
remaining three original prime normalizers act identically on that field. -/
theorem residue_action (i : Fin 4) (x : Reduction) :
    residue (reductionEquiv i x)=
      if i=1 then conjugation (residue x) else residue x := by
  have h3 : (3:F3)=0 := by decide
  fin_cases i <;> ext <;> norm_num [residue,reductionEquiv,forward,conjugation] <;> ring
  case «1».im => linear_combination x.imJ*h3

theorem norm_three_frobenius (x : Reduction) :
    residue (reductionEquiv 1 x)=(residue x)^3 := by
  rw [residue_action]
  simp only [ite_true,conjugation_frobenius]
end PELNormalizerResidueFrobenius318
