module
public import SourceFiniteBranch318
public section
noncomputable section
namespace SourceDenominatorCover318
open Polynomial LinearContactSquareclass318 FourRootPivot318
set_option maxHeartbeats 500000
@[expose] def untwisted (i:Fin 4) : ℚ[X]:=∏j:Fin 3,(X-C (contacts (indices i j.succ)))
@[expose] def weight : Fin 4→ℚ:=![1/843308032,-1/921600000,1/455386337280000,-1/9926634375]

/-- Literal Lagrange partition of unity at the four actual contacts. -/
theorem unity : ∑i:Fin 4,C (weight i)*untwisted i=1:=by
  apply Polynomial.funext
  intro x
  norm_num [weight,untwisted,indices,contacts,Fin.sum_univ_succ,Fin.prod_univ_succ]
  ring

variable (c:Fin 4→ℚˣ)
@[expose] def twistUnit (i:Fin 4) : ℚˣ:=∏j:Fin 3,c (indices i j.succ)
@[expose] def twisted (i:Fin 4) : ℚ[X]:=
  ∏j:Fin 3,ContactKummerOrder318.coefficient c (indices i j.succ)
@[expose] def denominator (i:Fin 4) : ContactKummerOrder318.SourceOrder c:=
  algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c) (twisted c i)

lemma twisted_factor (i:Fin 4) : twisted c i=C (twistUnit c i:ℚ)*untwisted i:=by
  simp only [twisted,ContactKummerOrder318.coefficient,Finset.prod_mul_distrib,
    ←map_prod,twistUnit,untwisted]
  simp

lemma untwisted_from_twisted (i:Fin 4) :
    untwisted i=C (↑(twistUnit c i)⁻¹:ℚ)*twisted c i:=by
  rw [twisted_factor,←mul_assoc,←map_mul,Units.inv_mul,map_one,one_mul]

/-- The actual three-other-branch denominators cover the whole original
four-root algebra. The arbitrary rational twists are retained as units. -/
theorem span_top : Ideal.span (Set.range (denominator c))=⊤:=by
  rw [Ideal.eq_top_iff_one]
  have h:=congrArg (algebraMap ℚ[X] (ContactKummerOrder318.SourceOrder c)) unity
  rw [map_sum,map_one] at h
  rw [←h]
  apply Ideal.sum_mem
  intro i _
  rw [map_mul,untwisted_from_twisted c i,map_mul]
  apply Ideal.mul_mem_left
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨i,rfl⟩

end SourceDenominatorCover318
