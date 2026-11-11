module
public import FiniteOverlapSheaves318
public section
noncomputable section
namespace FiniteGlobalFormCompatibility318
open AlgebraicGeometry CategoryTheory KaehlerDifferential
open FiniteInvariantDifferential318 CanonicalDifferentialSheafMap318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R : Type u} [CommRing R]

/-- Image of the actual x-chart invariant global section under the actual canonical sheaf map. -/
@[expose] def xGlobalImage (A B : R) :
    AffineDifferentialSheaf318.GlobalDifferentials (R:=R) (S:=CommonRing A B) := by
  letI : Algebra (XChart A B) (CommonRing A B) := (xMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (XChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((xMap A B).commutes r).symm
  exact (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap (XChart A B) (CommonRing A B)))
    (targetSheaf (R:=R) (T:=CommonRing A B))).hom
      ((moduleSpecΓFunctor.map (sheafMap (R:=R) (S:=XChart A B) (T:=CommonRing A B)))
        ((tilde.isoTop (R:=CommRingCat.of (XChart A B))
          (ModuleCat.of (XChart A B) (KaehlerDifferential R (XChart A B)))).hom (xForm A B)))

@[expose] def yGlobalImage (A B : R) :
    AffineDifferentialSheaf318.GlobalDifferentials (R:=R) (S:=CommonRing A B) := by
  letI : Algebra (YChart A B) (CommonRing A B) := (yMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (YChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((yMap A B).commutes r).symm
  exact (PushforwardGlobalSections318.globalIso (CommRingCat.ofHom (algebraMap (YChart A B) (CommonRing A B)))
    (targetSheaf (R:=R) (T:=CommonRing A B))).hom
      ((moduleSpecΓFunctor.map (sheafMap (R:=R) (S:=YChart A B) (T:=CommonRing A B)))
        ((tilde.isoTop (R:=CommRingCat.of (YChart A B))
          (ModuleCat.of (YChart A B) (KaehlerDifferential R (YChart A B)))).hom (yForm A B)))

theorem xGlobalImage_formula (A B : R) : xGlobalImage A B=
    (tilde.isoTop (R:=CommRingCat.of (CommonRing A B))
      (ModuleCat.of (CommonRing A B) (KaehlerDifferential R (CommonRing A B)))).hom (commonX A B) := by
  letI : Algebra (XChart A B) (CommonRing A B) := (xMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (XChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((xMap A B).commutes r).symm
  have h:=global_image (R:=R) (S:=XChart A B) (T:=CommonRing A B) (xForm A B)
  have hx : KaehlerDifferential.map R R (XChart A B) (CommonRing A B) (xForm A B)=commonX A B :=
    x_pullback A B
  rw [hx] at h
  exact h

theorem yGlobalImage_formula (A B : R) : yGlobalImage A B=
    (tilde.isoTop (R:=CommRingCat.of (CommonRing A B))
      (ModuleCat.of (CommonRing A B) (KaehlerDifferential R (CommonRing A B)))).hom (commonY A B) := by
  letI : Algebra (YChart A B) (CommonRing A B) := (yMap A B).toRingHom.toAlgebra
  letI : IsScalarTower R (YChart A B) (CommonRing A B) :=
    IsScalarTower.of_algebraMap_eq fun r => ((yMap A B).commutes r).symm
  have h:=global_image (R:=R) (S:=YChart A B) (T:=CommonRing A B) (yForm A B)
  have hy : KaehlerDifferential.map R R (YChart A B) (CommonRing A B) (yForm A B)=commonY A B :=
    y_pullback A B
  rw [hy] at h
  exact h

/-- Actual global-section equality after the genuine canonical sheaf transports. -/
theorem actual_global_compatibility (A B : R) : yGlobalImage A B=xGlobalImage A B := by
  rw [yGlobalImage_formula,xGlobalImage_formula,common_forms_equal]
end FiniteGlobalFormCompatibility318
