module
public import LocalizedModuleSheafFrame318
public import RankOneTargetNeighborhood318
public import ModuleFrameTransport318
public section
noncomputable section
namespace FiniteTargetSheafFrame318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R:CommRingCat.{u}} (M:(Spec R).Modules) [M.IsQuasicoherent] (a:R)
abbrev basic {R:CommRingCat.{u}} (a:R):(Spec R).Opens:=PrimeSpectrum.basicOpen a
lemma localization_square:
    (basicOpenIsoSpecAway a).inv≫(basic a).ι=
      LocalizedModuleSheafFrame318.schemeMap a:=by
  exact (Iso.inv_comp_eq (basicOpenIsoSpecAway a)).mpr
    (basicOpenIsoSpecAway_hom_SpecMap a).symm
/-- A genuine frame on the original principal open, transported through the
actual principal-localization Scheme isomorphism with its original inclusion. -/
@[expose] def openFrame {ι:Type u}
    (b:Module.Basis ι (Localization.Away a)
      (LocalizedModule.Away a (moduleSpecΓFunctor.obj M))):
    SheafOfModules.free (R:=((basic a).toScheme).ringCatSheaf) ι≅
      M.restrict (basic a).ι:=
  ModuleFrameTransport318.alongIso (basicOpenIsoSpecAway a).symm
    (M.restrict (basic a).ι) ι
    (LocalizedModuleSheafFrame318.frame M a b ≪≫
      (Scheme.Modules.restrictFunctorCongr (localization_square a).symm).app M ≪≫
      (Scheme.Modules.restrictFunctorComp (basicOpenIsoSpecAway a).inv
        (basic a).ι).app M)
/-- The rank-one specialization is an actual unit-sheaf isomorphism,
not merely an equality of local ranks. -/
@[expose] def unitFrame
    (b:Module.Basis (Fin 1) (Localization.Away a)
      (LocalizedModule.Away a (moduleSpecΓFunctor.obj M))):
    SheafOfModules.unit ((basic a).toScheme).ringCatSheaf≅
      M.restrict (basic a).ι:=
  (coproductUniqueIso (fun _:ULift.{u} (Fin 1)=>
    SheafOfModules.unit ((basic a).toScheme).ringCatSheaf)).symm ≪≫
      openFrame M a (b.reindex Equiv.ulift.symm)
lemma unitFrame_hom_inv
    (b:Module.Basis (Fin 1) (Localization.Away a)
      (LocalizedModule.Away a (moduleSpecΓFunctor.obj M))):
    (unitFrame M a b).hom≫(unitFrame M a b).inv=𝟙 _ :=(unitFrame M a b).hom_inv_id
lemma unitFrame_inv_hom
    (b:Module.Basis (Fin 1) (Localization.Away a)
      (LocalizedModule.Away a (moduleSpecΓFunctor.obj M))):
    (unitFrame M a b).inv≫(unitFrame M a b).hom=𝟙 _ :=(unitFrame M a b).inv_hom_id
variable (A B:CommRingCat.{u}) [Algebra A B] [Module.Finite A B]
    (N:(Spec B).Modules) [N.IsQuasicoherent]
    [Module.FinitePresentation B (moduleSpecΓFunctor.obj N)]
    [Module.Flat B (moduleSpecΓFunctor.obj N)]
    (rk:∀q:PrimeSpectrum B,Module.rankAtStalk (moduleSpecΓFunctor.obj N) q=1)
lemma whole_preimage (a:A):
    Spec.map (CommRingCat.ofHom (algebraMap A B))⁻¹ᵁPrimeSpectrum.basicOpen a=
      PrimeSpectrum.basicOpen (algebraMap A B a):=SpecMap_preimage_basicOpen _ _
include rk in
/-- Every target point has a genuine principal neighborhood whose entire
inverse image carries a unit frame for the unchanged original sheaf. The
finite-presentation, flatness and rank-one hypotheses are explicit inputs. -/
lemma exists_frame (p:PrimeSpectrum A):
    ∃a:A,p∈PrimeSpectrum.basicOpen a ∧ Nonempty
      (SheafOfModules.unit ((basic (algebraMap A B a)).toScheme).ringCatSheaf≅
        N.restrict (basic (algebraMap A B a)).ι):=by
  obtain ⟨a,ha,⟨b⟩⟩:=RankOneTargetNeighborhood318.exists_basis A B
    (moduleSpecΓFunctor.obj N) rk p
  exact ⟨a,ha,⟨unitFrame N (algebraMap A B a) b⟩⟩
end FiniteTargetSheafFrame318
