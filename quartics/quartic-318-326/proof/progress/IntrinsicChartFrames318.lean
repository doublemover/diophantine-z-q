module
public import IntrinsicChartSections318
public import RestrictedFrameLocal318
public import UnitLineDifferentials318
public section
noncomputable section
namespace IntrinsicChartFrames318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (h : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (e : KaehlerDifferential R S ≃ₗ[S] S)

@[expose] def frame : (Scheme.Modules.restrictFunctor j).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
    (FamilyIntrinsicDifferentials318.omega p).restrict j :=
  Scheme.Modules.restrictUnitIso j ≪≫ (AffineDifferentialSheaf318.frameIso e).symm ≪≫
    IntrinsicChartNormalization318.iso j p h

theorem frame_one (ω : KaehlerDifferential R S) (hω : e ω=1) :
    (frame j p h e).hom.val.app (op ⊤) (show Γ(Y,j ''ᵁ ⊤) from 1) =
      IntrinsicChartSections318.sectionMap j p h ω := by
  change moduleSpecΓFunctor.map (IntrinsicChartNormalization318.iso j p h).hom
    (moduleSpecΓFunctor.map (AffineDifferentialSheaf318.frameIso e).inv
      (moduleSpecΓFunctor.map (Scheme.Modules.restrictUnitIso j).hom
        (show Γ(Y,j ''ᵁ ⊤) from 1))) = _
  rw [UnitLineDifferentials318.restrictUnit_one, UnitLineDifferentials318.frame_inverse_one e ω hω]
  rfl

theorem generator_bijective (ω : KaehlerDifferential R S) (hω : e ω=1)
    (V : Y.Opens) (hV : V ≤ j ''ᵁ ⊤) :
    Function.Bijective (fun a : Γ(Y,V) =>
      a • (FamilyIntrinsicDifferentials318.omega p).presheaf.map (homOfLE hV).op
        (IntrinsicChartSections318.sectionMap j p h ω)) :=
  RestrictedFrameLocal318.generator_bijective j _ (frame j p h e)
    (IntrinsicChartSections318.sectionMap j p h ω) (frame_one j p h e ω hω) V hV
end IntrinsicChartFrames318
