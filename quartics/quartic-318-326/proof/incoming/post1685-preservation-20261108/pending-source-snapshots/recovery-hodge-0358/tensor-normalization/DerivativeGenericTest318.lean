module
public import ContactIntrinsicFrames318
public import ContactFrameNormalization318
public import UnitLineDifferentials318
public section
noncomputable section
namespace IntrinsicFrameDerivative318
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
#check UnitLineDifferentials318.frame_inverse_one
universe u
variable {Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (h : j ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (e : KaehlerDifferential R S ≃ₗ[S] S)

@[expose] def chartFrame :
    (FamilyIntrinsicDifferentials318.omega p).restrict j ≅
      SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf :=
  (IntrinsicChartNormalization318.iso j p h).symm ≪≫ AffineDifferentialSheaf318.frameIso e

#check chartFrame

/-- Exact frame value on the actual ambient universal derivative of the
chart coordinate, not an independently named abstract generator. -/
theorem chartFrame_D (s : S) (hs : e (KaehlerDifferential.D R S s)=1) :
    (chartFrame j p h e).hom.app ⊤
      ((FamilyIntrinsicDifferentials318.D p).d
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s))) =
      (show Γ(Spec (CommRingCat.of S),⊤) from 1) := by
  let f := IntrinsicChartNormalization318.iso j p h
  let g := AffineDifferentialSheaf318.frameIso e
  have hi := UnitLineDifferentials318.frame_inverse_one e (KaehlerDifferential.D R S s) hs
  have hd : (moduleSpecΓFunctor.map (chartFrame j p h e).inv)
      (show Γ(Spec (CommRingCat.of S),⊤) from 1) =
      (FamilyIntrinsicDifferentials318.D p).d
        ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv s)) := by
    change (moduleSpecΓFunctor.map (g.inv ≫ f.hom)) _ = _
    rw [Functor.map_comp]
    exact (congrArg (moduleSpecΓFunctor.map f.hom) hi).trans
      (IntrinsicChartNormalization318.differential j p h s)
  change (moduleSpecΓFunctor.map (chartFrame j p h e).hom) _ = _
  exact (congrArg (moduleSpecΓFunctor.map (chartFrame j p h e).hom) hd).symm.trans
    (CategoryTheory.Iso.inv_hom_id_apply (moduleSpecΓFunctor.mapIso (chartFrame j p h e)) _)

#check chartFrame_D

end IntrinsicFrameDerivative318
