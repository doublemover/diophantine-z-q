module
public import AllPrimePreparedFullSource318
public section
noncomputable section
namespace ContactPrimeForms318
open ThreeDetectorUniformFamily318
open scoped BigOperators
set_option maxHeartbeats 1000000

/-- Original five roots, in the literal source order. -/
@[expose] def root : Fin 5 → ℚ := ![0,-1/2,-1,1/2399,-32/407]
@[expose] def scaleRoot (labels : Fin 4 → ℤ) (j : Fin 3) : ℚ :=
  if j=0 then 1 else if j=1 then c₁ labels else c₂ labels
@[expose] def slope (labels : Fin 4 → ℤ) (i : Fin 3 × Fin 5) : ℚ :=
  -root i.2/(scaleRoot labels i.1)^2

lemma root_injective : Function.Injective root := by
  intro i j he
  fin_cases i <;> fin_cases j <;> norm_num [root] at he ⊢

lemma scaleRoot_ne (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) (j : Fin 3) :
    scaleRoot labels j≠0 := by
  fin_cases j
  · norm_num [scaleRoot]
  · exact FixedDetectorScales318.sum_ne labels hn
  · exact FixedDetectorScales318.normProduct_ne labels hn

lemma parameter_eq (labels : Fin 4 → ℤ) (t : ℚ) (j : Fin 3) :
    contactParameter labels t j=(scaleRoot labels j)^2*t := by
  fin_cases j <;> simp [contactParameter,scaleRoot,ScaledContactWeights318.parameter]

lemma contact_product (x : ℚ) : ContactWeightWitness318.contact x=∏ k : Fin 5, (x-root k) := by
  simp [Fin.prod_univ_succ,root,ContactWeightWitness318.contact]
  <;> ring

lemma slope_injective (labels : Fin 4 → ℤ) (hn : ∀ j, labels j≠0) (j : Fin 3) :
    Function.Injective (fun k => slope labels (j,k)) := by
  intro k l he
  apply root_injective
  have hd := pow_ne_zero 2 (scaleRoot_ne labels hn j)
  have he' : -root k= -root l := (div_left_inj' hd).mp he
  exact neg_injective he'

/-- The scalar factor is a square because the original scales and the common
contact denominator are squares. This retains all five distinct row factors. -/
lemma contact_scaled (c u z : ℚ) (hc : c≠0) (hz : z≠0) :
    ContactWeightWitness318.contact (c^2*(u/z^2))=
      (∏ k : Fin 5, (u+(-root k/c^2)*z^2)) * ((c/z)^5)^2 := by
  rw [contact_product]
  simp only [Fin.prod_univ_succ,root,Matrix.cons_val_zero,Matrix.cons_val_succ,
    Fin.succ_zero_eq_one]
  field_simp [hc,hz]
  <;> ring

end ContactPrimeForms318
