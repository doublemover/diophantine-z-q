module
public import FiniteTargetSheafFrame318
public section
noncomputable section
namespace AffinePrincipalLineFrame318
open AlgebraicGeometry CategoryTheory TopologicalSpace
set_option maxHeartbeats 600000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
@[expose] def alongIso {X Y:Scheme.{u}} (e:X≅Y) (M:Y.Modules)
    (frame:SheafOfModules.unit X.ringCatSheaf≅M.restrict e.hom):
    SheafOfModules.unit Y.ringCatSheaf≅M:=
  (Scheme.Modules.restrictUnitIso e.inv).symm ≪≫
    (Scheme.Modules.restrictFunctor e.inv).mapIso frame ≪≫
      ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm.app M) ≪≫
      ((Scheme.Modules.restrictFunctorCongr e.inv_hom_id).app M) ≪≫
      ((Scheme.Modules.restrictFunctorId (X:=Y)).app M)
variable {X:Scheme.{u}} (U:X.Opens) (hU:IsAffineOpen U) (a:Γ(X,U))
abbrev basic:(Spec Γ(X,U)).Opens:=PrimeSpectrum.basicOpen a
abbrev chartMap:(basic U a).toScheme⟶X:=(basic U a).ι≫hU.fromSpec
lemma chart_range:(chartMap U hU a).opensRange=X.basicOpen a:=by
  rw [Scheme.Hom.opensRange_comp,Scheme.Opens.opensRange_ι,hU.fromSpec_image_basicOpen]
/-- Actual same-range open-immersion isomorphism; neither open is replaced
by an abstract affine scheme with equal function field. -/
@[expose] def iso:(basic U a).toScheme≅(X.basicOpen a).toScheme:=
  IsOpenImmersion.isoOfRangeEq (chartMap U hU a) (X.basicOpen a).ι (by
    change ((chartMap U hU a).opensRange:Set X)=Set.range (X.basicOpen a).ι
    rw [chart_range,Scheme.Opens.range_ι])
lemma iso_square:(iso U hU a).hom≫(X.basicOpen a).ι=chartMap U hU a:=
  IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _
/-- Transport a line frame on the actual affine-Spec principal open to
the unchanged original ambient sheaf on the original principal open. -/
@[expose] def frame (M:X.Modules)
    (e:SheafOfModules.unit (basic U a).toScheme.ringCatSheaf≅
      (M.restrict hU.fromSpec).restrict (basic U a).ι):
    SheafOfModules.unit (X.basicOpen a).toScheme.ringCatSheaf≅
      M.restrict (X.basicOpen a).ι:=
  alongIso (iso U hU a) (M.restrict (X.basicOpen a).ι)
    (e ≪≫ ((Scheme.Modules.restrictFunctorComp (basic U a).ι hU.fromSpec).symm.app M) ≪≫
      ((Scheme.Modules.restrictFunctorCongr (iso_square U hU a).symm).app M) ≪≫
      ((Scheme.Modules.restrictFunctorComp (iso U hU a).hom (X.basicOpen a).ι).app M))
lemma frame_hom_inv (M:X.Modules)
    (e:SheafOfModules.unit (basic U a).toScheme.ringCatSheaf≅
      (M.restrict hU.fromSpec).restrict (basic U a).ι):
    (frame U hU a M e).hom≫(frame U hU a M e).inv=𝟙 _ :=(frame U hU a M e).hom_inv_id
lemma frame_inv_hom (M:X.Modules)
    (e:SheafOfModules.unit (basic U a).toScheme.ringCatSheaf≅
      (M.restrict hU.fromSpec).restrict (basic U a).ι):
    (frame U hU a M e).inv≫(frame U hU a M e).hom=𝟙 _ :=(frame U hU a M e).inv_hom_id
end AffinePrincipalLineFrame318
