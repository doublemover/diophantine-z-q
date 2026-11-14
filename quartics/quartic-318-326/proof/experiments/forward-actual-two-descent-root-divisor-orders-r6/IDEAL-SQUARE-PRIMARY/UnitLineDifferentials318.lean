module
public import InvariantChartCover318
public section
noncomputable section
namespace UnitLineDifferentials318
open AlgebraicGeometry CategoryTheory Opposite
open AffineDifferentialSheaf318
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]

/-- Genuine global unit section of the actual structure module sheaf. -/
@[expose] def unitSection (X : Scheme.{u}) : (SheafOfModules.unit X.ringCatSheaf).sections :=
  PresheafOfModules.sectionsMk (fun U => (show Γ(X,U.unop) from 1)) (by
    intro U V f
    change (X.presheaf.map f).hom 1=1
    exact map_one (X.presheaf.map f).hom)

theorem isoTop_one :
    (tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S S)).hom 1=
      (show Γ(Spec (CommRingCat.of S),⊤) from 1) := by
  change StructureSheaf.const (1:S) (1:S) ⊤ (by simp)=1
  exact StructureSheaf.const_one ⊤

/-- Restrict the actual global structure line and identify it with the genuine
local relative differential sheaf using an actual normalized module frame. -/
@[expose] def localIso {X : Scheme.{u}} (f : Spec (CommRingCat.of S) ⟶ X)
    [IsOpenImmersion f] (e : KaehlerDifferential R S ≃ₗ[S] S) :
    (Scheme.Modules.restrictFunctor f).obj (SheafOfModules.unit X.ringCatSheaf) ≅
      differentialSheaf (R:=R) (S:=S) :=
  Scheme.Modules.restrictUnitIso f ≪≫ (frameIso e).symm

theorem restrictUnit_one {X : Scheme.{u}} (f : Spec (CommRingCat.of S) ⟶ X)
    [IsOpenImmersion f] :
    (moduleSpecΓFunctor.map (Scheme.Modules.restrictUnitIso f).hom)
      (show Γ(X,f ''ᵁ ⊤) from 1)=(show Γ(Spec (CommRingCat.of S),⊤) from 1) := by
  change (f.appIso ⊤).hom.hom 1=1
  exact map_one (f.appIso ⊤).hom.hom

/-- The normalized inverse sheaf frame sends the actual unit section to the
specified universal-differential section. -/
theorem frame_inverse_one (e : KaehlerDifferential R S ≃ₗ[S] S)
    (ω : KaehlerDifferential R S) (hω : e ω=1) :
    (moduleSpecΓFunctor.map (frameIso e).inv) (show Γ(Spec (CommRingCat.of S),⊤) from 1)=
      (tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom ω := by
  apply (ConcreteCategory.bijective_of_isIso (moduleSpecΓFunctor.map (frameIso e).hom)).1
  have hn:=congrArg (fun g => g ω) (sheaf_frame_global_naturality e)
  simp only [ConcreteCategory.comp_apply,tildeSelf,CategoryTheory.Iso.refl_hom,
    Functor.map_id,CategoryTheory.id_apply] at hn
  change (moduleSpecΓFunctor.map (frameIso e).hom)
    ((tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom ω)=
      (tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S S)).hom (e ω) at hn
  rw [hω,isoTop_one] at hn
  have hc:=CategoryTheory.Iso.inv_hom_id_apply (moduleSpecΓFunctor.mapIso (frameIso e))
    (show Γ(Spec (CommRingCat.of S),⊤) from 1)
  exact hc.trans hn.symm

/-- The genuine restricted global unit section becomes the specified actual
invariant differential section under the normalized local O-module isomorphism. -/
theorem localIso_unit {X : Scheme.{u}} (f : Spec (CommRingCat.of S) ⟶ X)
    [IsOpenImmersion f] (e : KaehlerDifferential R S ≃ₗ[S] S)
    (ω : KaehlerDifferential R S) (hω : e ω=1) :
    (moduleSpecΓFunctor.map (localIso f e).hom)
      (show Γ(X,f ''ᵁ ⊤) from (unitSection X).val (op (f ''ᵁ ⊤)))=
        (tilde.isoTop (R:=CommRingCat.of S)
          (ModuleCat.of S (KaehlerDifferential R S))).hom ω := by
  change (moduleSpecΓFunctor.map ((Scheme.Modules.restrictUnitIso f).hom ≫ (frameIso e).inv))
      (show Γ(X,f ''ᵁ ⊤) from 1)=_
  rw [Functor.map_comp]
  change (moduleSpecΓFunctor.map (frameIso e).inv)
    ((moduleSpecΓFunctor.map (Scheme.Modules.restrictUnitIso f).hom) (show Γ(X,f ''ᵁ ⊤) from 1))=_
  rw [restrictUnit_one]
  exact frame_inverse_one e ω hω
end UnitLineDifferentials318
