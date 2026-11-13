module
public import NormalOverlapReciprocalDual318
public import NativeTildeLocalizedModule318
public import IntegralNormalFiniteDualSheafRestriction318
public import IntegralNormalInfinityDualSheafRestriction318
public section
noncomputable section
namespace NormalOverlapReciprocalDualSheaf318
open AlgebraicGeometry CategoryTheory IntegralOriginalNormalOverlap318
universe u
variable (R : Type u) [CommRing R] (a d : Fin 4 → R)
local notation "S" => LaurentCoordinateInversion318.Base R
local notation "A" => FiniteOverlap R a d
local notation "C" => InfinityOverlap R a d
local notation "E" => overlapEquiv R a d
local instance : Algebra S A := (IntegralClosureAlongRingMap318.scalar (finiteMap R a d)).toAlgebra
local instance : Algebra S C := (IntegralClosureAlongRingMap318.scalar (infinityMap R a d)).toAlgebra

@[expose] def map := Spec.map (CommRingCat.ofHom E.toRingHom)

/-- Native pullback of the OLD finite overlap dual is the OLD infinity
overlap dual. This is the full dual transport, before a differential twist. -/
@[expose] def iso :
    (Scheme.Modules.pullback (map R a d)).obj
      (IntegralNormalFiniteDualSheafRestriction318.overlapDual R a d) ≅
        IntegralNormalInfinityDualSheafRestriction318.overlapDual R a d :=
  NativeTildeLocalizedModule318.pullbackIso (CommRingCat.ofHom E.toRingHom)
    (ModuleCat.of A (FiniteDualModuleAction318.Dual S A))
    (ModuleCat.of C (FiniteDualModuleAction318.Dual S C))
    (NormalOverlapReciprocalDual318.moduleIso R a d)

lemma hom_formula : (iso R a d).hom=
    (TildePullback318.pullbackIso (CommRingCat.ofHom E.toRingHom)).hom.app
      (ModuleCat.of A (FiniteDualModuleAction318.Dual S A)) ≫
        (tilde.functor (CommRingCat.of C)).map
          (NormalOverlapReciprocalDual318.moduleIso R a d).hom := rfl
end NormalOverlapReciprocalDualSheaf318
