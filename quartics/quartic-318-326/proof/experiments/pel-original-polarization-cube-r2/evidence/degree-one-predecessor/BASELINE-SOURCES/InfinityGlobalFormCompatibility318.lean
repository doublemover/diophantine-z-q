module
public import InfinityOverlapSheaves318
public section
noncomputable section
namespace InfinityGlobalFormCompatibility318
open AlgebraicGeometry CategoryTheory KaehlerDifferential
open ActualDifferentialOverlap318 DifferentialChartMaps318 InvariantChartForms318 CanonicalDifferentialSheafMap318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

/-- Image of the actual finite-chart invariant global section under the actual canonical sheaf map. -/
@[expose] def finiteGlobalImage (A B : R) :
    AffineDifferentialSheaf318.GlobalDifferentials (R:=R) (S:=CommonRing A B) := by
  letI : Algebra (FiniteChart A B) (CommonRing A B) := (finiteChartMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (FiniteChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((finiteChartMap A B).commutes r).symm
  exact (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap (FiniteChart A B) (CommonRing A B)))
    (targetSheaf (R:=R) (T:=CommonRing A B))).hom
      ((moduleSpecΓFunctor.map (sheafMap (R:=R) (S:=FiniteChart A B) (T:=CommonRing A B)))
        ((tilde.isoTop (R:=CommRingCat.of (FiniteChart A B))
          (ModuleCat.of (FiniteChart A B) (KaehlerDifferential R (FiniteChart A B)))).hom (finite A B)))

@[expose] def infinityGlobalImage (A B : R) :
    AffineDifferentialSheaf318.GlobalDifferentials (R:=R) (S:=CommonRing A B) := by
  letI : Algebra (InfinityChart A B) (CommonRing A B) := (infinityChartMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (InfinityChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((infinityChartMap A B).commutes r).symm
  exact (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap (InfinityChart A B) (CommonRing A B)))
    (targetSheaf (R:=R) (T:=CommonRing A B))).hom
      ((moduleSpecΓFunctor.map (sheafMap (R:=R) (S:=InfinityChart A B) (T:=CommonRing A B)))
        ((tilde.isoTop (R:=CommRingCat.of (InfinityChart A B))
          (ModuleCat.of (InfinityChart A B) (KaehlerDifferential R (InfinityChart A B)))).hom (infinity A B)))

theorem finiteGlobalImage_formula (A B : R) : finiteGlobalImage A B=
    (tilde.isoTop (R:=CommRingCat.of (CommonRing A B))
      (ModuleCat.of (CommonRing A B) (KaehlerDifferential R (CommonRing A B)))).hom (finiteForm A B) := by
  letI : Algebra (FiniteChart A B) (CommonRing A B) := (finiteChartMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (FiniteChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((finiteChartMap A B).commutes r).symm
  have h:=global_image (R:=R) (S:=FiniteChart A B) (T:=CommonRing A B) (finite A B)
  have hx : KaehlerDifferential.map R R (FiniteChart A B) (CommonRing A B) (finite A B)=finiteForm A B :=
    finite_pullback A B
  rw [hx] at h
  exact h

theorem infinityGlobalImage_formula (A B : R) : infinityGlobalImage A B=
    (tilde.isoTop (R:=CommRingCat.of (CommonRing A B))
      (ModuleCat.of (CommonRing A B) (KaehlerDifferential R (CommonRing A B)))).hom (infinityForm A B) := by
  letI : Algebra (InfinityChart A B) (CommonRing A B) := (infinityChartMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (InfinityChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((infinityChartMap A B).commutes r).symm
  have h:=global_image (R:=R) (S:=InfinityChart A B) (T:=CommonRing A B) (infinity A B)
  have hy : KaehlerDifferential.map R R (InfinityChart A B) (CommonRing A B) (infinity A B)=infinityForm A B :=
    infinity_pullback A B
  rw [hy] at h
  exact h

/-- Actual global-section equality after the genuine canonical sheaf transports. -/
theorem actual_global_compatibility (A B : R) : infinityGlobalImage A B=finiteGlobalImage A B := by
  rw [infinityGlobalImage_formula,finiteGlobalImage_formula,←finiteForm_eq_infinityForm]
end InfinityGlobalFormCompatibility318
