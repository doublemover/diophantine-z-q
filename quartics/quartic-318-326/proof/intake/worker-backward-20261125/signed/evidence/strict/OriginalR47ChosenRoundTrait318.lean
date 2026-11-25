module
public import OriginalR47GlobalCentreRees318
public import OriginalR47TraitActualReesCentre318
public section
noncomputable section

namespace OriginalR47ChosenRoundTrait318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Set
open OriginalR47GlobalCentreRees318
open OriginalR47IsolatedCentreCover318 (Centre)
open OriginalR47TraitRoundKernel318
open OriginalR47TraitAffineCentre318 (B carriedIdeal chart carried_on_trait)
open OriginalAffineReesBlowup318 (blowup projection)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
variable {R : Type u} [CommRing R] {X : Scheme.{u}}
variable (s : X ⟶ base (R:=R))
variable (Z : Set X) (hZ : Z.Finite) (hC : ∀ x ∈ Z, IsClosed ({x} : Set X))
variable (pick : ∀ z : Z, Centre Z z) (z : Z)
local notation "j" => affineArrow pick z
local notation "P" => PrimeSpectrum.asIdeal (marked pick z)
local notation "p" => PrimeSpectrum.asIdeal (s (Subtype.val z))
local notation "r" => proj Z hZ hC pick

variable {Z} in
/-- The actual original centre's affine map after applying the old
family's structural morphism. Neither the base prime nor its scalar is
a free input. -/
abbrev oldScalar : Algebra R (A pick z) :=
  (Spec.preimage (j ≫ s)).hom.toAlgebra

variable {Z} in
theorem old_scalar_read :
    letI := oldScalar s pick z
    Spec.algebraMap R (A pick z) = j ≫ s :=
  Spec.map_preimage (j ≫ s)

/-- The first exact shared bridge for the old/global ω comparison.
Here i is the actual chart of the same relative gluing colimit, and l
is its genuine entire base change along the original non-finite-type
arithmetic trait. The old/global commutation uses the original
structural map, not just equality on a reduced closed fibre. -/
theorem attached :
    letI : Algebra R (A pick z) := oldScalar s pick z
    let v := OriginalR47TraitAffineCentre318.chart p s j (old_scalar_read s pick z)
    ∃ i : blowup P ⟶ source Z hZ hC pick,
      IsPullback i (projection P) r j ∧
      ∃ l : blowup (carriedIdeal p P) ⟶ Yp p s r,
        IsPullback l (projection (carriedIdeal p P)) (a p s r) v ∧
        l ≫ b p s r = OriginalR47TraitActualReesCentre318.affRees p P ≫ i := by
  let : Algebra R (A pick z) := oldScalar s pick z
  obtain ⟨i,Hi⟩ := OriginalR47GlobalCentreRees318.chart Z hZ hC pick z
  exact ⟨i,Hi,OriginalR47TraitActualReesCentre318.actual_chart p s r j
    (old_scalar_read s pick z) P i Hi⟩

end OriginalR47ChosenRoundTrait318

#print axioms OriginalR47ChosenRoundTrait318.old_scalar_read
#print axioms OriginalR47ChosenRoundTrait318.attached
