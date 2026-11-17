module
public import ClearedContactForms318
public section
noncomputable section
namespace ActualContactPrimeSquareclasses318
open ContactPrimeForms318 ClearedContactForms318
open scoped BigOperators
set_option maxHeartbeats 1000000
variable {labels : Fin 4 → ℤ} (C : Clearing labels)

@[expose] def squareFactor (q : ℚ) (h : ℤ) (u w : ℤ) (j : Fin 3) : ℚ :=
  (scaleRoot labels j/((C.denominator:ℚ)*(w:ℚ)))^5 *
    ThreeDetectorUniformFamily318.squareFactor q labels h (parameter C u w) j

lemma contact (hn : ∀ j, labels j≠0) (u w : ℤ) (hw : w≠0) (j : Fin 3) :
    ContactWeightWitness318.contact
      (ThreeDetectorUniformFamily318.contactParameter labels (parameter C u w) j)=
      (rowProduct C u w j:ℚ)*(scaleRoot labels j/((C.denominator:ℚ)*(w:ℚ)))^10 := by
  have hD : (C.denominator:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt C.positive
  have hwQ : (w:ℚ)≠0 := by exact_mod_cast hw
  rw [parameter_eq]
  have he := contact_scaled (scaleRoot labels j) (u:ℚ)
    ((C.denominator:ℚ)*(w:ℚ)) (scaleRoot_ne labels hn j) (mul_ne_zero hD hwQ)
  have hp : (rowProduct C u w j:ℚ)=
      ∏ k : Fin 5, ((u:ℚ)+(-root k/(scaleRoot labels j)^2)*
        ((C.denominator:ℚ)*(w:ℚ))^2) := by
    simp only [rowProduct,Int.cast_prod]
    apply Finset.prod_congr rfl
    intro k _
    exact value_exact C u w (j,k)
  rw [hp]
  simpa only [parameter,←pow_mul] using he

/-- All three actual stored pole inputs have the five selected integer
factors as squareclass. Neither h nor the trace quotient is substituted. -/
theorem witness (hn : ∀ j, labels j≠0) (q : ℚ) (h u w : ℤ) (hw : w≠0) (j : Fin 3) :
    ThreeDetectorUniformFamily318.witness q labels h (parameter C u w) (190+51*j.val)=
      (rowProduct C u w j:ℚ)*(squareFactor C q h u w j)^2 := by
  rw [ThreeDetectorUniformFamily318.witness_squareclass,contact C hn u w hw j]
  dsimp [squareFactor]
  ring

lemma squareFactor_ne (hn : ∀ j, labels j≠0) (q : ℚ) (h u w : ℤ) (hw : w≠0) (j : Fin 3)
    (hb : 0<ThreeDetectorUniformFamily318.witness q labels h (parameter C u w) (190+51*j.val)) :
    squareFactor C q h u w j≠0 := by
  intro he
  rw [witness C hn q h u w hw j,he] at hb
  norm_num at hb

/-- Exact valuation transfer, including2 and denominator primes: there is
no good-prime exclusion and no unproved claim that the square factor is a unit. -/
lemma valuation (v : AddValuation ℚ (WithTop ℤ)) (hn : ∀ j, labels j≠0)
    (q : ℚ) (h u w : ℤ) (hw : w≠0) (j : Fin 3) :
    v (ThreeDetectorUniformFamily318.witness q labels h (parameter C u w) (190+51*j.val))=
      v (rowProduct C u w j:ℚ)+2•v (squareFactor C q h u w j) := by
  rw [witness C hn q h u w hw j,v.map_mul,v.map_pow]

end ActualContactPrimeSquareclasses318
