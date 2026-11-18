module
public import OriginalIntegerReciprocalNormalization318
public import GenericOpenPushout318
public section
noncomputable section
namespace OriginalIntegerClosureGluing318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ)

/-- Actual gluing of the two parameter integral closures inside the original
Kummer field along their identical Laurent integral closure. This alone is
not a proof of regularity, properness, or normalization of the whole-order
proper model; the reciprocal order comparison and finite map remain. -/
abbrev model : Scheme := pushout
  (OriginalIntegerNormalizedOverlap318.intoFinite c)
  (OriginalIntegerReciprocalNormalization318.intoInfinity c)

@[expose] def finiteChart : Spec (CommRingCat.of (OriginalIntegerFiniteClosure318.Closure c)) ⟶
    model c := pushout.inl _ _
@[expose] def infinityChart : Spec (CommRingCat.of (OriginalIntegerReciprocalNormalization318.Closure c)) ⟶
    model c := pushout.inr _ _

instance finiteChart_open : IsOpenImmersion (finiteChart c) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (OriginalIntegerNormalizedOverlap318.intoFinite c)
      (OriginalIntegerReciprocalNormalization318.intoInfinity c)) WalkingSpan.left))
instance infinityChart_open : IsOpenImmersion (infinityChart c) := by
  exact inferInstanceAs (IsOpenImmersion
    (colimit.ι (span (OriginalIntegerNormalizedOverlap318.intoFinite c)
      (OriginalIntegerReciprocalNormalization318.intoInfinity c)) WalkingSpan.right))

theorem intersection_square : IsPullback
    (OriginalIntegerNormalizedOverlap318.intoFinite c)
    (OriginalIntegerReciprocalNormalization318.intoInfinity c)
    (finiteChart c) (infinityChart c) := GenericOpenPushout318.square _ _

end OriginalIntegerClosureGluing318
