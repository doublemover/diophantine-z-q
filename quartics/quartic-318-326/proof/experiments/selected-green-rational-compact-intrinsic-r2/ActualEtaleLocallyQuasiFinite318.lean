module
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.RingTheory.Unramified.Field
public section
noncomputable section

namespace ActualEtaleLocallyQuasiFinite318
open AlgebraicGeometry CategoryTheory

/-- Each actual ring-theoretic fiber of an étale algebra is finite:
it is étale over the corresponding residue field, hence a free
formally unramified algebra of essentially finite type. -/
theorem ring_quasiFinite {R T : Type*} [CommRing R] [CommRing T]
    (f : R →+* T) (h : f.Etale) : f.QuasiFinite := by
  letI : Algebra R T := f.toAlgebra
  letI : Algebra.Etale R T := h.toAlgebra
  change Algebra.QuasiFinite R T
  constructor
  intro P hP
  letI : P.IsPrime := hP
  exact Algebra.FormallyUnramified.finite_of_free P.ResidueField (P.Fiber T)

theorem locallyQuasiFinite {X Y : Scheme} (f : X ⟶ Y) [Etale f] :
    LocallyQuasiFinite f where
  quasiFinite_appLE := fun {U} hU {V} hV e =>
    ring_quasiFinite _ (f.etale_appLE hU hV e)

end ActualEtaleLocallyQuasiFinite318
