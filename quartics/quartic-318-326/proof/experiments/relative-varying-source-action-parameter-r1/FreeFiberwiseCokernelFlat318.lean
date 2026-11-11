module
public import ResidueFiberRetraction318
public import FreeFiniteSplitCoordinates318
public section
namespace FreeFiberwiseCokernelFlat318
universe u
variable {R A B Q : Type u} [CommRing R]
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup Q]
  [Module R A] [Module R B] [Module R Q]

/-- For a map from a free module into a projective module, injectivity on
ALL maximal residue-field fibers implies universal tensor injectivity.
The proof constructs finite split coordinates, actual residue inverses,
lifts them, and uses determinant witnesses in the scalar-retraction ideal.
No Noetherian, finite-rank, reduced-base or flat-residue-field assumption. -/
lemma tensor_injective (f : A →ₗ[R] B) [Module.Free R A] [Module.Projective R B]
    (hf : ∀ m : Ideal R, ∀ _ : m.IsMaximal,
      Function.Injective (f.baseChange (R ⧸ m)))
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective (f.lTensor N) := by
  apply ResidueRetractionLift318.tensor_injective f _ N
  intro s m hm
  letI : m.IsMaximal := hm
  obtain ⟨n, e, r, he, hs⟩ := FreeFiniteSplitCoordinates318.exists_split s
  obtain ⟨ℓ, hℓ⟩ := ResidueFiberRetraction318.exists_retraction f m (hf m hm) n e r he
  exact ⟨n, e, ℓ, hs, hℓ⟩

/-- A genuine fieldwise flat-cokernel theorem with its module hypotheses
explicit. This discharges universal injectivity rather than requiring it
from the caller. Actual chart freeness/projectivity and exact residue
section comparison are still required to apply it to the contact family. -/
lemma flat (f : A →ₗ[R] B) (q : B →ₗ[R] Q)
    (he : Function.Exact f q) (hq : Function.Surjective q)
    [Module.Free R A] [Module.Projective R B] [Module.Flat R B]
    (hf : ∀ m : Ideal R, ∀ _ : m.IsMaximal,
      Function.Injective (f.baseChange (R ⧸ m))) : Module.Flat R Q :=
  UniversallyInjectiveCokernelFlat318.flat f q he hq (tensor_injective f hf)
end FreeFiberwiseCokernelFlat318
