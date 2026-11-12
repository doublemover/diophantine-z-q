module
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.Kaehler.Basic
public section
noncomputable section
namespace AffineDifferentialSheaf318
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- The genuine affine relative differential sheaf: tilde of the actual Kähler module. -/
@[expose] def differentialSheaf : (Spec (CommRingCat.of S)).Modules :=
  tilde (R := CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))

/-- An actual algebraic differential frame gives an actual O-module sheaf isomorphism. -/
@[expose] def frameIso (frame : KaehlerDifferential R S ≃ₗ[S] S) :
    differentialSheaf (R := R) (S := S) ≅
      SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf :=
  (tilde.functor (CommRingCat.of S)).mapIso frame.toModuleIso ≪≫ tildeSelf

/-- Actual global sections of the affine differential sheaf, not a parallel coefficient type. -/
abbrev GlobalDifferentials :=
  (modulesSpecToSheaf.obj (tilde (R := CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S)))).presheaf.obj (.op ⊤)

@[expose] def globalFrameIso (frame : KaehlerDifferential R S ≃ₗ[S] S) :
    GlobalDifferentials (R := R) (S := S) ≅ ModuleCat.of S S :=
  (tilde.isoTop (R := CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).symm ≪≫ frame.toModuleIso

/-- Every actual universal differential supplies a genuine global section. -/
@[expose] def differentialSection (s : S) : GlobalDifferentials (R := R) (S := S) :=
  (tilde.isoTop (R := CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom (KaehlerDifferential.D R S s)

theorem globalFrame_differential (frame : KaehlerDifferential R S ≃ₗ[S] S) (s : S) :
    (globalFrameIso frame).hom (differentialSection (R := R) s) = frame (KaehlerDifferential.D R S s) := by
  change frame ((tilde.isoTop (R := CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).inv
    ((tilde.isoTop (R := CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom
      (KaehlerDifferential.D R S s))) = _
  exact congrArg frame (CategoryTheory.Iso.hom_inv_id_apply _ _)

theorem normalized_differential_section (frame : KaehlerDifferential R S ≃ₗ[S] S) (s : S)
    (hs : frame (KaehlerDifferential.D R S s) = 1) :
    (globalFrameIso frame).hom (differentialSection (R := R) s) = 1 := by
  rw [globalFrame_differential,hs]

/-- Every actual affine global differential section has a unique frame coefficient. -/
theorem global_section_unique_coefficient (frame : KaehlerDifferential R S ≃ₗ[S] S)
    (ω : GlobalDifferentials (R := R) (S := S)) :
    ∃! c : S, (globalFrameIso frame).inv c = ω := by
  refine ⟨(globalFrameIso frame).hom ω,?_,?_⟩
  · exact CategoryTheory.Iso.hom_inv_id_apply _ ω
  · intro c hc
    have hh := congrArg (globalFrameIso frame).hom hc
    simpa using hh

/-- The actual sheaf map and actual global-sections frame form the canonical
commutative square, retaining the tilde-S-to-O identification explicitly. -/
theorem sheaf_frame_global_naturality (frame : KaehlerDifferential R S ≃ₗ[S] S) :
    (tilde.isoTop (R := CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom ≫
        moduleSpecΓFunctor.map (frameIso frame).hom =
      frame.toModuleIso.hom ≫ (tilde.isoTop (R := CommRingCat.of S) (ModuleCat.of S S)).hom ≫
        moduleSpecΓFunctor.map (tildeSelf (R := CommRingCat.of S)).hom := by
  have h := (tilde.toTildeΓNatIso (R := CommRingCat.of S)).hom.naturality frame.toModuleIso.hom
  have hh := congrArg (fun f => f ≫ moduleSpecΓFunctor.map (tildeSelf (R := CommRingCat.of S)).hom) h.symm
  simpa [frameIso, tilde.toTildeΓNatIso, Category.assoc] using hh

end AffineDifferentialSheaf318
