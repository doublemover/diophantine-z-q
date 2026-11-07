module
public import UnitPlaceOddSigns318
public import BadSeven318
public section
namespace ActualOddProductHeight318
open ConcreteG8Domain LocalGenerator318 NumberField
set_option maxHeartbeats 0
noncomputable section

/-- Full finite-place sign theorem for the actual odd multiples. -/
theorem finite_common_sign {ι:Type*} (w:FinitePlace K)
    (s:Finset ι) (n:ι→ℤ) (hn:∀i∈s,Odd (n i)) :
    (∀i∈s,w ((n i • P).xRep 0)≤1) ∨ (∀i∈s,1≤w ((n i • P).xRep 0)) := by
  have hD: w D≤1 := (ActualDuplicationPlaces318.finite_coefficients w).1
  rcases lt_or_eq_of_le hD with hlt|heq
  · exact Or.inr (fun i _=>BadSeven318.all_multiples w hlt (n i))
  · exact UnitPlaceOddSigns318.unit_place_common_sign_finset w heq s n hn

/-- The complete manuscript odd-index product-height identity, on the
actual number-field absolute height and actual elliptic multiples. -/
theorem odd_multiple_height_product {ι:Type*} (s:Finset ι) (n:ι→ℤ)
    (hn:∀i∈s,Odd (n i)) :
    NumberField.absLogHeight₁ (∏i∈s,((n i) • P).xRep 0)=
      ∑i∈s,GlobalSaturationHeight318.xHeight ((n i) • P) :=
  OddProductHeight318.odd_multiple_height_product s n hn (fun w=>finite_common_sign w s n hn)

#print axioms finite_common_sign
#print axioms odd_multiple_height_product
end
end ActualOddProductHeight318
