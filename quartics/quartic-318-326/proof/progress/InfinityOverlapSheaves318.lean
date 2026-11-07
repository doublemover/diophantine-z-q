module
public import ActualInfinityOpen318
public section
noncomputable section
namespace InfinityOverlapSheaves318
open AlgebraicGeometry CategoryTheory KaehlerDifferential
open ActualDifferentialOverlap318 DifferentialChartMaps318 ActualInfinityOpen318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

/-- A genuine O-module differential-sheaf restriction isomorphism on the actual
    source finite/infinity overlap, with all map hypotheses derived. -/
@[expose] def finiteRestrictionIso (A B : R) :
    letI := finite_open A B
    (Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom (finiteChartMap A B).toRingHom))).obj
      (AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=FiniteChart A B)) ≅
        AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=CommonRing A B) := by
  letI := finite_open A B
  letI : Algebra (FiniteChart A B) (CommonRing A B) := (finiteChartMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (FiniteChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((finiteChartMap A B).commutes r).symm
  letI : Algebra.FormallyEtale (FiniteChart A B) (CommonRing A B) :=
    finite_formallyEtale A B
  exact EtaleDifferentialSheaf318.restrictionIso

/-- The corresponding genuine differential restriction from the actual infinity Jacobian chart. -/
@[expose] def infinityRestrictionIso (A B : R) :
    letI := infinity_open A B
    (Scheme.Modules.restrictFunctor (Spec.map (CommRingCat.ofHom (infinityChartMap A B).toRingHom))).obj
      (AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=InfinityChart A B)) ≅
        AffineDifferentialSheaf318.differentialSheaf (R:=R) (S:=CommonRing A B) := by
  letI := infinity_open A B
  letI : Algebra (InfinityChart A B) (CommonRing A B) := (infinityChartMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (InfinityChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((infinityChartMap A B).commutes r).symm
  letI : Algebra.FormallyEtale (InfinityChart A B) (CommonRing A B) :=
    infinity_formallyEtale A B
  exact EtaleDifferentialSheaf318.restrictionIso
end InfinityOverlapSheaves318
