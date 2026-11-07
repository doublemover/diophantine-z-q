module
public import EvenContactEtale318
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public section
noncomputable section
namespace EvenContactCover318
open CategoryTheory AlgebraicGeometry EvenContactEtale318
set_option maxHeartbeats 0
universe u
variable {R:Type u} [CommRing R]

@[expose] def cover (u:Rˣ) : Scheme := Spec (CommRingCat.of (RootRing u))
@[expose] def structureMap (u:Rˣ) : cover u ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (RootRing u)))

/-- The actual spectrum of the normalized quadratic root ring is finite etale. -/
theorem finite_etale (u:Rˣ) (h2:IsUnit (2:R)) :
    IsFinite (structureMap u) ∧ Etale (structureMap u) := by
  constructor
  · apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr (rootRing_finite u)
  · apply (HasRingHomProperty.Spec_iff (P:=@Etale)).mpr
    exact RingHom.etale_algebraMap.mpr (rootRing_etale u h2)

/-- This is a genuine covering map, not only an etale empty scheme. -/
theorem flat_surjective [Nontrivial R] (u:Rˣ) :
    Flat (structureMap u) ∧ Surjective (structureMap u) := by
  apply (flat_and_surjective_SpecMap_iff _).mpr
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr (rootRing_faithfullyFlat u)

@[expose] def pointMap (u:Rˣ) (L:Type u) [Field L] [Algebra R L]
    (f:RootRing u→ₐ[R]L) : Spec (CommRingCat.of L) ⟶ cover u :=
  Spec.map (CommRingCat.ofHom f.toRingHom)

/-- The algebraic point factorization is over the actual base scheme. -/
theorem pointMap_structure (u:Rˣ) (L:Type u) [Field L] [Algebra R L]
    (f:RootRing u→ₐ[R]L) :
    pointMap u L f ≫ structureMap u =
      Spec.map (CommRingCat.ofHom (algebraMap R L)) := by
  unfold pointMap structureMap cover
  rw [←Spec.map_comp]
  congr 1
  ext r
  exact f.commutes r

end EvenContactCover318
