module
public import ActualDVRCompletion318
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public section
noncomputable section
namespace CompletionDescent318
open ActualDVRCompletion318 IsLocalRing
variable (R:Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The actual completion map is faithfully flat, hence supports actual
faithfully-flat descent; no unspecified faithful-flat comparison is assumed. -/
theorem completion_faithfullyFlat : Module.FaithfullyFlat R (Completion R) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- The canonical residue-field map, not an arbitrarily chosen residue isomorphism. -/
@[expose] def residueEquiv : ResidueField R ≃+* ResidueField (Completion R) :=
  RingEquiv.ofBijective (ResidueField.map (algebraMap R (Completion R)))
    (AdicCompletion.residueField_map_bijective R)

theorem residueEquiv_map (r:R) :
    residueEquiv R (residue R r)=residue (Completion R) (algebraMap R (Completion R) r) :=
  ResidueField.map_residue _ _

end CompletionDescent318
