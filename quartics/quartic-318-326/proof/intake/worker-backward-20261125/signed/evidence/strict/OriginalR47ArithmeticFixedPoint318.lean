module
public import OriginalR47TraitRoundKernel318
public section
noncomputable section

namespace OriginalR47InitialArithmeticAtlas318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalR47TraitRoundKernel318
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : Type} [CommRing R]
variable {X : Scheme} (s : X ⟶ base (R:=R))

abbrev fixedPrime (x : X) := (s x).asIdeal

/-- The unique old point at the closed point of its *own* actual
arithmetic localization. An independently chosen prime, residue
extension, or new selected mark is not an input. -/
theorem point_exists (x : X) :
    ∃ t : restricted (fixedPrime s x) s,
      forgetMap (fixedPrime s x) s t = x ∧
      toTrait (fixedPrime s x) s t =
        IsLocalRing.closedPoint (Localization.AtPrime (fixedPrime s x)) :=
  (lift_at_prime (fixedPrime s x) s x (PrimeSpectrum.ext rfl)).exists

@[expose] def fixedPoint (x : X) : restricted (fixedPrime s x) s :=
  (point_exists s x).choose

theorem fixedPoint_old (x : X) : forgetMap (fixedPrime s x) s (fixedPoint s x) = x :=
  (point_exists s x).choose_spec.1

theorem fixedPoint_trait (x : X) :
    toTrait (fixedPrime s x) s (fixedPoint s x) =
      IsLocalRing.closedPoint (Localization.AtPrime (fixedPrime s x)) :=
  (point_exists s x).choose_spec.2

theorem eq_fixedPoint (x : X) (t : restricted (fixedPrime s x) s)
    (ht : forgetMap (fixedPrime s x) s t = x) : t = fixedPoint s x := by
  let : IsPreimmersion (forgetMap (fixedPrime s x) s) :=
    forgetMap_preimmersion (fixedPrime s x) s
  exact (forgetMap (fixedPrime s x) s).isEmbedding.injective (ht.trans (fixedPoint_old s x).symm)

end OriginalR47InitialArithmeticAtlas318

#print axioms OriginalR47InitialArithmeticAtlas318.point_exists
#print axioms OriginalR47InitialArithmeticAtlas318.eq_fixedPoint
