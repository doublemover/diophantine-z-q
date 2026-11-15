module
public import PELOriginalRosatiPositiveForms318
public import PELOriginalFiniteIntegralProductSections318
public import FiniteSeparateFunctionExpansion318
public section
noncomputable section
namespace PELOriginalRosatiDoubleExpansion318
open QuaternionicRealPeriod318 PELPrincipalOrderCoordinates318
open PELOriginalComplementaryHermitian318 PELOriginalRosatiPositiveForms318
open PELOriginalLevelTheta318 PELOriginalLevelPowerSections318 PELOriginalWholeSectionSpanning318
variable (τ : ℂ) (hτ : 0 < τ.im) (a : order) (N : ℕ) [NeZero N]
abbrev leftDegree := N*firstWeight a
abbrev rightDegree := N*secondWeight a
local instance leftNonzero : NeZero (leftDegree a N) := ⟨by
  dsimp [leftDegree,firstWeight]; positivity⟩
local instance rightNonzero : NeZero (rightDegree a N) := ⟨by
  dsimp [rightDegree,secondWeight]; positivity⟩
@[expose] def value (side : Bool) (i : Fin 9 → Label N) (z w : ComplexVectors) : ℂ :=
  ∏ k,PELOriginalLevelPowerSections318.value τ hτ N (i k) (argument a side z w k)
lemma first_span (side : Bool) (i : Fin 9 → Label N) (w : ComplexVectors) :
    ∃ c : Label (leftDegree a N) → ℂ,∀ z,value τ hτ a N side i z w=
      ∑ k,c k*PELOriginalLevelPowerSections318.value τ hτ (leftDegree a N) k z :=
  PELOriginalFiniteIntegralProductSections318.span τ hτ (first a side)
    (fun k => linear (second a side k) w) (firstWeight a)
    (fun z l => first_form τ hτ a side z w l) (first_diagonal τ hτ a side) (first_phase τ hτ a side) N i
lemma second_span (side : Bool) (i : Fin 9 → Label N) (z : ComplexVectors) :
    ∃ c : Label (rightDegree a N) → ℂ,∀ w,value τ hτ a N side i z w=
      ∑ k,c k*PELOriginalLevelPowerSections318.value τ hτ (rightDegree a N) k w := by
  have hf : ∀ w l,∑ k,PELOriginalHermitianForm318.form τ hτ
      (linear (second a side k) w+linear (first a side k) z) (linear (second a side k) l)=
        (secondWeight a:ℂ)*PELOriginalHermitianForm318.form τ hτ w l := by
    intro w l
    simpa only [add_comm] using second_form τ hτ a side z w l
  obtain ⟨c,hc⟩ := PELOriginalFiniteIntegralProductSections318.span τ hτ (second a side)
    (fun k => linear (first a side k) z) (secondWeight a) hf (second_diagonal τ hτ a side) (second_phase τ hτ a side) N i
  exact ⟨c,fun w => by simpa only [value,argument,PELOriginalFiniteIntegralProductSections318.value,add_comm] using hc w⟩
lemma exists_coefficients (side : Bool) (i : Fin 9 → Label N) :
    ∃ C : Label (leftDegree a N) → Label (rightDegree a N) → ℂ,∀ z w,
      value τ hτ a N side i z w=∑ u,∑ v,C u v*
        PELOriginalLevelPowerSections318.value τ hτ (leftDegree a N) u z*
        PELOriginalLevelPowerSections318.value τ hτ (rightDegree a N) v w :=
  FiniteSeparateFunctionExpansion318.exists_double_expansion
    (PELOriginalLevelPowerSections318.value τ hτ (leftDegree a N))
    (PELOriginalLevelPowerSections318.value τ hτ (rightDegree a N))
    (original_values_independent τ hτ (leftDegree a N)) (value τ hτ a N side i)
    (first_span τ hτ a N side i) (second_span τ hτ a N side i)
@[expose] def coefficients (side : Bool) (i : Fin 9 → Label N) :=
  (exists_coefficients τ hτ a N side i).choose
lemma formula (side : Bool) (i : Fin 9 → Label N) (z w : ComplexVectors) :
    value τ hτ a N side i z w=∑ u,∑ v,coefficients τ hτ a N side i u v*
      PELOriginalLevelPowerSections318.value τ hτ (leftDegree a N) u z*
      PELOriginalLevelPowerSections318.value τ hτ (rightDegree a N) v w :=
  (exists_coefficients τ hτ a N side i).choose_spec z w
end PELOriginalRosatiDoubleExpansion318
