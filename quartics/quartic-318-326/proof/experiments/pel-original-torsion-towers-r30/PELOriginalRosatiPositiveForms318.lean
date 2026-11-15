module
public import PELOriginalOrderHermitianAdjoint318
public import Mathlib.Data.Fin.VecNotation
public section
noncomputable section
namespace PELOriginalRosatiPositiveForms318
open QuaternionicRealPeriod318 PELPrincipalOrderCoordinates318
open PELOriginalComplementaryOrder318 PELOriginalComplementaryHermitian318
open PELOriginalOrderHermitianAdjoint318 PELOriginalHermitianForm318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order)
@[expose] def first (side : Bool) : Fin 9 → order :=
  if side then ![a,1,0,a,complement a,complement a,0,0,0]
  else ![1,a,0,a,complement a,complement a,0,0,0]
@[expose] def second (side : Bool) : Fin 9 → order :=
  if side then ![1,0,adjoint a,-1,0,0,complement (adjoint a),adjoint a,complement (adjoint a)]
  else ![adjoint a,0,1,-1,0,0,complement (adjoint a),adjoint a,complement (adjoint a)]
@[expose] def argument (side : Bool) (z w : ComplexVectors) (i : Fin 9) : ComplexVectors :=
  linear (first a side i) z+linear (second a side i) w
abbrev firstWeight := 2*degree a+1
abbrev secondWeight := 2*degree (adjoint a)+2
lemma first_form (side : Bool) (z w l : ComplexVectors) :
    ∑ i : Fin 9,form τ hτ (argument a side z w i) (linear (first a side i) l)=
      (firstWeight a : ℂ)*form τ hτ z l := by
  have hc := hermitian_complement τ hτ a z l
  have ha := hermitian_adjoint τ hτ a l w
  have har : form τ hτ (linear (adjoint a) w) l=form τ hτ w (linear a l) := by
    rw [hermitian,←ha,hermitian,star_star]
  cases side <;>
    simp [argument,first,second,Fin.sum_univ_succ,
      linear_zero,linear_one,linear_neg_one,zero_add,add_zero,form_add_left,
      form_zero_first,form_zero_second,form_neg_first,form_neg_second] <;>
    dsimp [firstWeight]
  · push_cast
    linear_combination 2*hc+har
  · push_cast
    linear_combination 2*hc
lemma second_form (side : Bool) (z w l : ComplexVectors) :
    ∑ i : Fin 9,form τ hτ (argument a side z w i) (linear (second a side i) l)=
      (secondWeight a : ℂ)*form τ hτ w l := by
  have hc := hermitian_complement τ hτ (adjoint a) w l
  have ha := hermitian_adjoint τ hτ a z l
  cases side <;>
    simp [argument,first,second,Fin.sum_univ_succ,
      linear_zero,linear_one,linear_neg_one,zero_add,add_zero,form_add_left,
      form_zero_first,form_zero_second,form_neg_first,form_neg_second] <;>
    dsimp [secondWeight]
  · push_cast
    linear_combination 2*hc-ha
  · push_cast
    linear_combination 2*hc
lemma first_diagonal (side : Bool) (l : ComplexVectors) :
    ∑ i : Fin 9,form τ hτ (linear (first a side i) l) (linear (first a side i) l)=
      (firstWeight a : ℂ)*form τ hτ l l := by
  simpa only [argument,map_zero,add_zero] using first_form τ hτ a side l 0 l
lemma second_diagonal (side : Bool) (l : ComplexVectors) :
    ∑ i : Fin 9,form τ hτ (linear (second a side i) l) (linear (second a side i) l)=
      (secondWeight a : ℂ)*form τ hτ l l := by
  simpa only [argument,map_zero,zero_add] using second_form τ hτ a side 0 l l
open PELOriginalComplementaryAutomorphy318 PELOriginalPolarizationAutomorphy318
open PELOriginalPolarizationSemicharacter318 PELPeriodRiemannForm318
lemma action_zero (l : L τ hτ) : latticeAction τ hτ (0:order) l=0 := by
  apply Subtype.ext
  exact linear_zero l.val
lemma action_one (l : L τ hτ) : latticeAction τ hτ (1:order) l=l := by
  apply Subtype.ext
  exact linear_one l.val
lemma action_neg_one (l : L τ hτ) : latticeAction τ hτ (-1:order) l= -l := by
  apply Subtype.ext
  exact linear_neg_one l.val
lemma first_phase (side : Bool) (l : L τ hτ) : ∃ k : ℤ,
    (∑ i : Fin 9,quadratic ((latticeEquiv τ hτ).symm (latticeAction τ hτ (first a side i) l)))-
      (firstWeight a:ℤ)*quadratic ((latticeEquiv τ hτ).symm l)=2*k := by
  refine ⟨quadratic ((latticeEquiv τ hτ).symm (latticeAction τ hτ a l))+
    quadratic ((latticeEquiv τ hτ).symm (latticeAction τ hτ (complement a) l))-
    (degree a:ℤ)*quadratic ((latticeEquiv τ hτ).symm l),?_⟩
  cases side <;> simp [first,firstWeight,Fin.sum_univ_succ,action_zero,action_one,
    map_zero,quadratic] <;> ring
lemma second_phase (side : Bool) (l : L τ hτ) : ∃ k : ℤ,
    (∑ i : Fin 9,quadratic ((latticeEquiv τ hτ).symm (latticeAction τ hτ (second a side i) l)))-
      (secondWeight a:ℤ)*quadratic ((latticeEquiv τ hτ).symm l)=2*k := by
  refine ⟨quadratic ((latticeEquiv τ hτ).symm (latticeAction τ hτ (adjoint a) l))+
    quadratic ((latticeEquiv τ hτ).symm (latticeAction τ hτ (complement (adjoint a)) l))-
    (degree (adjoint a):ℤ)*quadratic ((latticeEquiv τ hτ).symm l),?_⟩
  cases side <;> simp [second,secondWeight,Fin.sum_univ_succ,action_zero,action_one,
    action_neg_one,map_zero,map_neg,quadratic_neg,quadratic] <;> ring
end PELOriginalRosatiPositiveForms318
