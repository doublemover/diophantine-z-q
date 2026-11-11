module
public import PullbackScalar318
public section
noncomputable section
namespace PullbackAdjointUnitFrame318
open AlgebraicGeometry CategoryTheory
universe u
variable {X Y:Scheme.{u}} (f:X⟶Y) (B:Y.Modules) (M:X.Modules)
    (e:SheafOfModules.unit Y.ringCatSheaf≅B)
    (d:(Scheme.Modules.pullback f).obj B⟶M)
/-- The actual pulled unit frame, with the canonical unit comparison.
It is not chosen by a generic-fiber or degree argument. -/
@[expose] def frame:SheafOfModules.unit X.ringCatSheaf≅
    (Scheme.Modules.pullback f).obj B:=
  (IdentityCotangent318.pullbackUnitIso f).symm≪≫(Scheme.Modules.pullback f).mapIso e
/-- The actual adjunction pins the image of the pulled generator to the
image of the ORIGINAL base generator. This equality is on whole module
sheaves, before evaluation on any affine chart or localization. -/
theorem adjoint_frame:
    StructurePushforwardSplit318.unitMap f≫
      (Scheme.Modules.pushforward f).map ((frame f B e).hom≫d)=
    e.hom≫(Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ d:=by
  rw [←PullbackScalar318.adjoint_unit,
    ←Adjunction.homEquiv_naturality_right]
  simp only [frame,Iso.trans_hom,Iso.symm_hom,Functor.mapIso_hom,
    ←Category.assoc,Iso.hom_inv_id,Category.id_comp]
  rw [Adjunction.homEquiv_naturality_left]
/-- Evaluating the actual sheaf identity at one retains the same source
section on EVERY base open, not just at the generic point. -/
theorem generator_image(U:Y.Opens):
    d.app (f⁻¹ᵁU) ((frame f B e).hom.app (f⁻¹ᵁU) 1)=
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ d).app U
        (e.hom.app U 1):=by
  have h:=congrArg (fun q=>q.app U 1) (adjoint_frame f B M e d)
  change d.app (f⁻¹ᵁU) ((frame f B e).hom.app (f⁻¹ᵁU) (f.app U 1))=
    ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ d).app U
      (e.hom.app U 1) at h
  simpa only [map_one] using h
end PullbackAdjointUnitFrame318
