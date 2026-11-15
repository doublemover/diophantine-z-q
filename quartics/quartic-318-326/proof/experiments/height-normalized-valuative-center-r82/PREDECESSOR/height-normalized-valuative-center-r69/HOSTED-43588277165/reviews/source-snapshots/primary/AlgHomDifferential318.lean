module
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.Tactic
public section
noncomputable section
namespace AlgHomDifferential318
open KaehlerDifferential
variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T]

/-- Genuine universal-differential pullback along an arbitrary algebra homomorphism. -/
@[expose] def map (f : S →ₐ[R] T) : KaehlerDifferential R S →ₗ[R] KaehlerDifferential R T := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact (KaehlerDifferential.map R R S T).restrictScalars R

@[simp] theorem map_D (f : S →ₐ[R] T) (s : S) :
    map f (D R S s) = D R T (f s) := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  exact KaehlerDifferential.map_D R R S T s

theorem map_smul (f : S →ₐ[R] T) (s : S) (ω : KaehlerDifferential R S) :
    map f (s • ω) = f s • map f ω := by
  letI : Algebra S T := f.toRingHom.toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r => (f.commutes r).symm
  change KaehlerDifferential.map R R S T (s • ω) =
    algebraMap S T s • KaehlerDifferential.map R R S T ω
  rw [LinearMap.map_smul, IsScalarTower.algebraMap_smul]
end AlgHomDifferential318
