module
public import ProductOverlapOpen318
public import FiniteInvariantDifferential318
public section
noncomputable section
namespace FiniteOverlapSheaves318
open AlgebraicGeometry CategoryTheory KaehlerDifferential
open ShortAffineJacobian318 FiniteInvariantDifferential318 ProductOverlapOpen318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

/-- The actual finite x-Jacobian overlap morphism is an open immersion. -/
theorem x_open (A B : R) : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (xMap A B).toRingHom)) :=
  actual_left_spec_open (R:=R) _ _
/-- The actual finite y-Jacobian overlap morphism is an open immersion. -/
theorem y_open (A B : R) : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (yMap A B).toRingHom)) :=
  actual_right_spec_open (R:=R) _ _

/-- A genuine O-module differential-sheaf restriction isomorphism on the actual
    source finite x-Jacobian overlap, with all map hypotheses derived. -/
@[expose] def xRestrictionIso (A B : R) :
    letI := x_open A B
    (Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom (xMap A B).toRingHom))).obj
      (AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=XChart A B)) ≅
        AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=CommonRing A B) := by
  letI := x_open A B
  letI : Algebra (XChart A B) (CommonRing A B) := (xMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (XChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((xMap A B).commutes r).symm
  letI : Algebra.FormallyEtale (XChart A B) (CommonRing A B) :=
    left_formallyEtale (presentation A B 0).jacobian (presentation A B 1).jacobian
  exact EtaleDifferentialSheaf318.restrictionIso

/-- The corresponding genuine differential restriction from the actual y-Jacobian chart. -/
@[expose] def yRestrictionIso (A B : R) :
    letI := y_open A B
    (Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom (yMap A B).toRingHom))).obj
      (AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=YChart A B)) ≅
        AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=CommonRing A B) := by
  letI := y_open A B
  letI : Algebra (YChart A B) (CommonRing A B) := (yMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (YChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((yMap A B).commutes r).symm
  letI : Algebra.FormallyEtale (YChart A B) (CommonRing A B) :=
    right_formallyEtale (presentation A B 0).jacobian (presentation A B 1).jacobian
  exact EtaleDifferentialSheaf318.restrictionIso
end FiniteOverlapSheaves318
