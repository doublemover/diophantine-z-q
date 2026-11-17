module
public import ActualContactPrimeSquareclasses318
public import TwoTwistPointRealization318
public section
noncomputable section
namespace ActualFourPoleClassMatching318
open TwoTwistPointRealization318

/-- The exact residual rational-point obligation at b=C*z². Both curves
share n; the second twist is the actual complement, not a chosen substitute. -/
structure MatchedPoints (b C : ℚ) where
  n : ℚ
  first : SquareclassPoint (17*C) n
  second : SquareclassPoint (17*C) (n*(1-b/17))

/-- Exact factor matching, conditional on genuine rational points. This is
not an existence theorem for MatchedPoints. Zero ordinates and n=0 remain allowed. -/
def fromFactor (b C z : ℚ) (hb : b≠0) (hz : z≠0)
    (hfactor : b=C*z^2) (P : MatchedPoints b C) : Realization b where
  β := 17*C
  θ := 1-b/17
  c := z
  d := 17*b
  n := P.n
  c_ne := hz
  d_ne := mul_ne_zero (by norm_num) hb
  first_class := by rw [hfactor]; ring
  second_class := by ring
  first := P.first
  second := P.second

variable {labels : Fin 4 → ℤ}

/-- The same contact row product, actual trace quotient, h and CRT parameter.
No positive-squareclass representative is substituted for the stored pole. -/
def contact (C : ClearedContactForms318.Clearing labels)
    (hn : ∀ j, labels j≠0) (q : ℚ) (h u w : ℤ) (hw : w≠0) (j : Fin 3)
    (hb : 0<ThreeDetectorUniformFamily318.witness q labels h
      (ClearedContactForms318.parameter C u w) (190+51*j.val))
    (P : MatchedPoints
      (ThreeDetectorUniformFamily318.witness q labels h
        (ClearedContactForms318.parameter C u w) (190+51*j.val))
      (ClearedContactForms318.rowProduct C u w j:ℚ)) :
    Realization (ThreeDetectorUniformFamily318.witness q labels h
      (ClearedContactForms318.parameter C u w) (190+51*j.val)) :=
  fromFactor _ _ (ActualContactPrimeSquareclasses318.squareFactor C q h u w j)
    (ne_of_gt hb)
    (ActualContactPrimeSquareclasses318.squareFactor_ne C hn q h u w hw j hb)
    (ActualContactPrimeSquareclasses318.witness C hn q h u w hw j) P

/-- Exact factorization of the fourth stored pole retains factor11 and the
same detector witness. This does not assert a rational point on either twist. -/
lemma scalar_factor (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ) :
    PreparedIntegerSource318.scalarB q labels h =
      (11*ScalarForwardWitness318.inputR q)*
        (102*ScalarForwardWitness318.quotient
          (DetectorGateWitness318.witness q labels h) (labels 1))^2 := by
  simpa only [PreparedIntegerSource318.scalarB,
    DetectorGateWitness318.witness_input] using
    ScalarForwardWitness318.pole_squareclass_eleven
      (DetectorGateWitness318.witness q labels h) (labels 1)

def scalar (q : ℚ) (labels : Fin 4 → ℤ) (h : ℤ)
    (hb : 0<PreparedIntegerSource318.scalarB q labels h)
    (P : MatchedPoints (PreparedIntegerSource318.scalarB q labels h)
      (11*ScalarForwardWitness318.inputR q)) :
    Realization (PreparedIntegerSource318.scalarB q labels h) := by
  let z := 102*ScalarForwardWitness318.quotient
    (DetectorGateWitness318.witness q labels h) (labels 1)
  have hf : PreparedIntegerSource318.scalarB q labels h =
      (11*ScalarForwardWitness318.inputR q)*z^2 := scalar_factor q labels h
  have hz : z≠0 := by
    intro he
    rw [hf,he] at hb
    norm_num at hb
  exact fromFactor _ _ z (ne_of_gt hb) hz hf P

/-- Joint class-matching at the one actual h and t. The four remaining
rational-point inputs are explicit, so this is assembly, not their producer. -/
def four (C : ClearedContactForms318.Clearing labels)
    (hn : ∀ j, labels j≠0) (q : ℚ) (h u w : ℤ) (hw : w≠0)
    (hb : ∀ j : Fin 3, 0<ThreeDetectorUniformFamily318.witness q labels h
      (ClearedContactForms318.parameter C u w) (190+51*j.val))
    (hs : 0<PreparedIntegerSource318.scalarB q labels h)
    (P : ∀ j : Fin 3, MatchedPoints
      (ThreeDetectorUniformFamily318.witness q labels h
        (ClearedContactForms318.parameter C u w) (190+51*j.val))
      (ClearedContactForms318.rowProduct C u w j:ℚ))
    (Q : MatchedPoints (PreparedIntegerSource318.scalarB q labels h)
      (11*ScalarForwardWitness318.inputR q)) :
    (∀ j : Fin 3, Realization (ThreeDetectorUniformFamily318.witness q labels h
      (ClearedContactForms318.parameter C u w) (190+51*j.val))) ×
    Realization (PreparedIntegerSource318.scalarB q labels h) :=
  ⟨fun j => contact C hn q h u w hw j (hb j) (P j), scalar q labels h hs Q⟩

end ActualFourPoleClassMatching318
