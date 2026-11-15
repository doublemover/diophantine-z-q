module
public import OriginalSeparatedOddCanonical318
public import OriginalContactSeparation210318
public section
noncomputable section
namespace OriginalOutside210Canonical318
open NumberField OriginalPointFinitePlaceRoots318 OriginalAllPlaceNormalizedData318
variable (c : Fin 4 → ℚˣ) (tau : ℚ) (w : FinitePlace (K c tau)) (D : Data c tau w)
local notation "V" => OriginalPointFinitePlaceRoots318.V c tau w
local notation "a" => IntegralSourceBranches318.contacts V

lemma unit210 (hw : w (210:K c tau)=1) : IsUnit (210:V) := by
  let U : Vˣ := ActualFinitePlaceIntegers318.unitOfNormOne w (210:K c tau) hw
  have he : (U:V)=210 := by
    apply IsFractionRing.injective V (K c tau)
    rw [ActualFinitePlaceIntegers318.unitOfNormOne_value,map_ofNat]
  exact he ▸ U.isUnit

/-- For every actual finite place not dividing210, all local smooth
canonical extension data are PRODUCED from the same original point.
There is no remaining parity, pivot, unit-twist, contact-separation or
coordinate-integrality hypothesis in this consumer. Global regular-model
Hodge and KS identifications remain distinct. -/
theorem exists_extension (hw : w (210:K c tau)=1) :
    (∃ he : ∀ k,D.exponent k=0,∃ i,Nonempty (OriginalEvenFiniteCanonicalExtension318.Extension c tau w D he i)) ∨
    (∃ i,∃ hi : D.exponent i=1,Nonempty (OriginalFinitePivotCanonicalExtension318.Extension c tau w D i hi)) ∨
    (∃ he : ∀ k,D.exponent k=0,Nonempty (OriginalEvenCanonicalExtension318.Extension c tau w D he)) ∨
    (∃ ho : ∀ k,D.exponent k=1,Nonempty (OriginalCommonOddCanonicalExtension318.Extension c tau w D ho)) := by
  have hu := unit210 c tau w hw
  have h2 := OriginalContactSeparation210318.two_unit V hu
  have hs := OriginalContactSeparation210318.contacts_separated V hu
  rcases OriginalSeparatedOddCanonical318.exists_extension c tau w D h2 hs with ⟨ht,h⟩|⟨ht,h⟩
  · rcases h with he|ho
    · exact Or.inl he
    · exact Or.inr (Or.inl ho)
  · exact Or.inr (Or.inr h)
end OriginalOutside210Canonical318
