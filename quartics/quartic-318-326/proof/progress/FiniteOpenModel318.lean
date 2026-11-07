module
public import FiniteAffineOrder318
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import OpenJModel318
public section
noncomputable section
namespace FiniteOpenModel318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R Rf B:Type u} [CommRing R] [CommRing Rf] [CommRing B]
  [Algebra R Rf] [Algebra R B] [Algebra Rf B] [IsScalarTower R Rf B]
  (d:R) [IsLocalization.Away d Rf] [Module.Finite Rf B]

include Rf in
/-- A finite suborder selected from the proved denominator-clearing construction. -/
@[expose] def order : Subalgebra R B :=
  (FiniteAffineOrder318.finite_order_of_open_cover (Rf:=Rf) (B:=B) d).choose

instance order_finite : Module.Finite R (order (Rf:=Rf) (B:=B) d) :=
  (FiniteAffineOrder318.finite_order_of_open_cover (Rf:=Rf) (B:=B) d).choose_spec.1

instance order_localization : IsLocalization.Away
    (algebraMap R (order (Rf:=Rf) (B:=B) d) d) B :=
  (FiniteAffineOrder318.finite_order_of_open_cover (Rf:=Rf) (B:=B) d).choose_spec.2

abbrev model : Scheme := Spec (CommRingCat.of (order (Rf:=Rf) (B:=B) d))
@[expose] def structureMap : model (Rf:=Rf) (B:=B) d ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (algebraMap R (order (Rf:=Rf) (B:=B) d)))

/-- A genuinely finite morphism, not finiteness inferred from integrality. -/
instance structure_finite : IsFinite (structureMap (Rf:=Rf) (B:=B) d) := by
  apply (IsFinite.SpecMap_iff _).mpr
  exact RingHom.finite_algebraMap.mpr inferInstance

/-- Properness is relative to the affine base; no compactification of that base is claimed. -/
instance structure_proper : IsProper (structureMap (Rf:=Rf) (B:=B) d) := inferInstance

@[expose] def openMap : Spec (CommRingCat.of B) ⟶ model (Rf:=Rf) (B:=B) d :=
  Spec.map (CommRingCat.ofHom (algebraMap (order (Rf:=Rf) (B:=B) d) B))
instance open_immersion : IsOpenImmersion (openMap (Rf:=Rf) (B:=B) d) :=
  IsOpenImmersion.of_isLocalization (algebraMap R (order (Rf:=Rf) (B:=B) d) d)

@[expose] def denominatorOpen : (model (Rf:=Rf) (B:=B) d).Opens :=
  PrimeSpectrum.basicOpen (algebraMap R (order (Rf:=Rf) (B:=B) d) d)

theorem open_range : Set.range (openMap (Rf:=Rf) (B:=B) d)=
    (denominatorOpen (Rf:=Rf) (B:=B) d).carrier :=
  PrimeSpectrum.localization_away_comap_range B _

/-- Actual recovery of the original cover as an open scheme in the finite model. -/
@[expose] def openIso : Spec (CommRingCat.of B) ≅
    (denominatorOpen (Rf:=Rf) (B:=B) d).toScheme :=
  IsOpenImmersion.isoOfRangeEq (openMap (Rf:=Rf) (B:=B) d)
    (denominatorOpen (Rf:=Rf) (B:=B) d).ι
    (by rw [Scheme.Opens.range_ι]; exact open_range d)

theorem openIso_hom_fac : (openIso (Rf:=Rf) (B:=B) d).hom ≫
    (denominatorOpen (Rf:=Rf) (B:=B) d).ι=openMap (Rf:=Rf) (B:=B) d := by
  unfold openIso
  exact IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _

/-- Actual compatibility with the original algebra map to the affine base. -/
theorem open_structure : openMap (Rf:=Rf) (B:=B) d ≫ structureMap d=
    Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  unfold openMap structureMap model
  rw [←Spec.map_comp]
  congr 1

end FiniteOpenModel318

namespace OpenJFiniteModel318
open CategoryTheory AlgebraicGeometry
variable (N:ℕ) (B:Type) [CommRing B]
  [Algebra (OpenJModel318.Base N) B] [Algebra (Polynomial ℤ) B]
  [IsScalarTower (Polynomial ℤ) (OpenJModel318.Base N) B]
  [Module.Finite (OpenJModel318.Base N) B]

/-- The actual finite affine model over the entire integral j-line. -/
abbrev model := FiniteOpenModel318.model (Rf:=OpenJModel318.Base N) (B:=B)
  (OpenJModel318.denominator N)
abbrev structureMap := FiniteOpenModel318.structureMap (Rf:=OpenJModel318.Base N) (B:=B)
  (OpenJModel318.denominator N)
instance structure_finite : IsFinite (structureMap N B) := inferInstance
instance structure_proper : IsProper (structureMap N B) := inferInstance
/-- The actual original algebra is recovered by inverting precisely 6N*j*(j−1728). -/
@[expose] def originalOpenIso : Spec (CommRingCat.of B) ≅
    (FiniteOpenModel318.denominatorOpen (Rf:=OpenJModel318.Base N) (B:=B)
      (OpenJModel318.denominator N)).toScheme :=
  FiniteOpenModel318.openIso (Rf:=OpenJModel318.Base N) (B:=B) (OpenJModel318.denominator N)
end OpenJFiniteModel318
