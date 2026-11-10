module
public import PELNormalizerReductionAction318
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
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp <;> ring

/-- Finite Frobenius is verified on the actual quadratic residue carrier. -/
theorem conjugation_frobenius (x : Residue) : conjugation x=x^3 := by
  obtain ⟨r,s⟩ := x
  fin_cases r <;> fin_cases s <;> ext <;>
    norm_num [conjugation,pow_succ,pow_two]

theorem conjugation_nontrivial : conjugation (QuadraticAlgebra.omega:Residue)≠
    (QuadraticAlgebra.omega:Residue) := by
  intro h
  have hh := congrArg QuadraticAlgebra.im h
  norm_num [conjugation,QuadraticAlgebra.omega] at hh

/-- Only the actual norm3 representative acts by Frobenius onF9. The
remaining three original prime normalizers act identically on that field. -/
theorem residue_action (i : Fin 4) (x : Reduction) :
    residue (reductionEquiv i x)=
      if i=1 then conjugation (residue x) else residue x := by
  fin_cases i <;> ext <;> norm_num [residue,reductionEquiv,forward,conjugation] <;> ring

theorem norm_three_frobenius (x : Reduction) :
    residue (reductionEquiv 1 x)=(residue x)^3 := by
  rw [residue_action]
  simp only [ite_true,conjugation_frobenius]
end PELNormalizerResidueFrobenius318
