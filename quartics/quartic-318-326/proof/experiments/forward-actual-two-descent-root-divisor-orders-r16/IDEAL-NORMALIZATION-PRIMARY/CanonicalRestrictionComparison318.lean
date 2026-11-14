module
public import CanonicalEtaleComparison318
public section
noncomputable section
namespace CanonicalRestrictionComparison318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

/-- The actual open-restriction/pullback comparison respects the genuine sheaf adjunctions. -/
theorem restriction_pullback_adjoint {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (N : X.Modules) (e : (Scheme.Modules.pullback f).obj M ⟶ N) :
    (Scheme.Modules.restrictAdjunction f).homEquiv _ _
      ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M ≫ e)=
        (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ e := by
  rw [Adjunction.homEquiv_naturality_right]
  change (Scheme.Modules.restrictAdjunction f).homEquiv _ _
    (((Scheme.Modules.restrictAdjunction f).leftAdjointUniq
      (Scheme.Modules.pullbackPushforwardAdjunction f)).hom.app M) ≫ _ = _
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rfl

variable {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
  [Algebra.FormallyEtale S T]
  [IsOpenImmersion (CanonicalDifferentialSheafMap318.baseMap (S:=S) (T:=T))]

/-- The actual étale differential restriction isomorphism has exactly the canonical
    universal-derivative sheaf map as its adjoint. -/
theorem restriction_adjoint :
    (Scheme.Modules.restrictAdjunction
      (CanonicalDifferentialSheafMap318.baseMap (S:=S) (T:=T))).homEquiv _ _
        (EtaleDifferentialSheaf318.restrictionIso (R:=R) (S:=S) (T:=T)).hom =
      CanonicalDifferentialSheafMap318.sheafMap (R:=R) (S:=S) (T:=T) := by
  change (Scheme.Modules.restrictAdjunction _).homEquiv _ _
    ((Scheme.Modules.restrictFunctorIsoPullback _).hom.app _ ≫
      (EtaleDifferentialSheaf318.pullbackIso (R:=R) (S:=S) (T:=T)).hom)=_
  rw [restriction_pullback_adjoint,CanonicalEtaleComparison318.pullback_adjoint]

/-- Literal equality of actual sheaf morphisms closes the map/isomorphism identification. -/
theorem restrictionIso_hom_eq :
    (EtaleDifferentialSheaf318.restrictionIso (R:=R) (S:=S) (T:=T)).hom =
      CanonicalDifferentialSheafMap318.restrictionMap (R:=R) (S:=S) (T:=T) := by
  apply ((Scheme.Modules.restrictAdjunction
    (CanonicalDifferentialSheafMap318.baseMap (S:=S) (T:=T))).homEquiv _ _).injective
  rw [restriction_adjoint,CanonicalDifferentialSheafMap318.adjoint_restrictionMap]

/-- Actual canonical differential restriction is an isomorphism, not an assumed input. -/
theorem canonical_restriction_isIso : IsIso
    (CanonicalDifferentialSheafMap318.restrictionMap (R:=R) (S:=S) (T:=T)) := by
  rw [←restrictionIso_hom_eq]
  infer_instance
end CanonicalRestrictionComparison318
