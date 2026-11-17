module
public import ActualTwoDescentOriginalIdealAffineRestriction318
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Ideal
public section
noncomputable section
namespace ActualTwoDescentLocalizedIdealTensorEquivalence318
open scoped TensorProduct
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] (I : Ideal R)

/-- Localization of the original ideal as an ACTUAL submodule of S.
The native localized-submodule instance supplies the universal property. -/
def idealTensorToLocalized : S ⊗[R] I ≃ₗ[S]
    Submodule.localized' S M (Algebra.linearMap R S) I :=
  (IsLocalizedModule.isBaseChange M S (I.toLocalized' S M (Algebra.linearMap R S))).equiv

/-- The actual scalar extension is the actual extended ideal, not a
separate isomorphic rank-one object. No flatness premise is left supplied. -/
def localizedIdealTensorEquiv : S ⊗[R] I ≃ₗ[S] I.map (algebraMap R S) :=
  (idealTensorToLocalized S M I).trans
    (LinearEquiv.ofEq _ _ (Ideal.localized'_eq_map S M I))

/-- The canonical comparison sends s tensor x to exactly s*image(x).
This fixes the normalization needed for subsequent sheaf comparisons. -/
lemma actual_localized_ideal_tensor_value (s : S) (x : I) :
    (localizedIdealTensorEquiv S M I (s ⊗ₜ[R] x) : S)=s*algebraMap R S (x:R) := by
  change (idealTensorToLocalized S M I (s ⊗ₜ[R] x) : S)=_
  rw [idealTensorToLocalized,IsBaseChange.equiv_tmul]
  rfl
end ActualTwoDescentLocalizedIdealTensorEquivalence318
