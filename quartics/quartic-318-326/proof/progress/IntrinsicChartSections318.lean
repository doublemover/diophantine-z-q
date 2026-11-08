module
public import IntrinsicChartNormalization318
public import OpenChartSections318
public import KaehlerAdditiveExt318
public import AlgHomDifferential318
public section
noncomputable section
namespace IntrinsicChartSections318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

/-- The affine scalar action on a restricted sheaf is precisely multiplication
by the corresponding actual ambient regular function. -/
theorem chart_smul {Y : Scheme.{u}} {S : CommRingCat.{u}} (j : Spec S ⟶ Y)
    [IsOpenImmersion j] (M : Y.Modules) (s : S) (m : Γ(M,j ''ᵁ ⊤)) :
    (show Γ(M,j ''ᵁ ⊤) from s • (show Γ(M.restrict j,⊤) from m)) =
      (j.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv s) • m := by
  change (j.appIso ⊤).inv ((Spec S).presheaf.map (𝟙 (op ⊤)) ((Scheme.ΓSpecIso S).inv s)) • m = _
  have h := congrArg (fun k => k ((Scheme.ΓSpecIso S).inv s)) ((Spec S).presheaf.map_id (op ⊤))
  exact congrArg (fun a : Γ(Spec S,⊤) => (j.appIso ⊤).inv a • m) h

variable {Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (h : j ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R S)))

/-- Every ordinary chart differential gives an actual intrinsic ambient section
over the chart image. -/
@[expose] def sectionMap : KaehlerDifferential R S →+ Γ(FamilyIntrinsicDifferentials318.omega p,j ''ᵁ ⊤) :=
  (moduleSpecΓFunctor.map (IntrinsicChartNormalization318.iso j p h).hom).hom.toAddMonoidHom.comp
    (tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom.hom.toAddMonoidHom

theorem section_D (s : S) :
    sectionMap j p h (KaehlerDifferential.D R S s) =
      (FamilyIntrinsicDifferentials318.D p).d
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) :=
  IntrinsicChartNormalization318.differential j p h s

theorem section_smul (s : S) (ω : KaehlerDifferential R S) :
    sectionMap j p h (s • ω) =
      (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s) • sectionMap j p h ω := by
  let q : ModuleCat.of S (KaehlerDifferential R S) ⟶
      moduleSpecΓFunctor.obj ((FamilyIntrinsicDifferentials318.omega p).restrict j) :=
    (tilde.isoTop (R:=CommRingCat.of S) (ModuleCat.of S (KaehlerDifferential R S))).hom ≫
      moduleSpecΓFunctor.map (IntrinsicChartNormalization318.iso j p h).hom
  exact (q.hom.map_smul s ω).trans
    (chart_smul j (FamilyIntrinsicDifferentials318.omega p) s (q ω))

end IntrinsicChartSections318
