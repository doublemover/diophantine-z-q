module
public import IntrinsicFrameDerivative318
public import TensorSheafNormalization318
public import IntrinsicTensorChartSections318
public import RestrictedFrameLocal318
public section
noncomputable section
namespace IntrinsicTensorGenerator318
open AlgebraicGeometry CategoryTheory Opposite
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u
variable {Y : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (j : Spec (CommRingCat.of S) ⟶ Y) [IsOpenImmersion j]
    (p : Y ⟶ Spec (CommRingCat.of R))
    (h : j ≫ p=Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (e : KaehlerDifferential R S ≃ₗ[S] S)

@[expose] def frame :
    (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
      (FamilyIntrinsicDifferentials318.omega p)).restrict j ≅
      SheafOfModules.unit (Spec (CommRingCat.of S)).ringCatSheaf :=
  TensorOpenRestriction318.iso j (FamilyIntrinsicDifferentials318.omega p)
    (FamilyIntrinsicDifferentials318.omega p) ≪≫
      TensorSheafFunctor318.congr (IntrinsicFrameDerivative318.chartFrame j p h e)
        (IntrinsicFrameDerivative318.chartFrame j p h e) ≪≫ TensorSheafFunctor318.unitIso

theorem frame_pure (m n : Γ(FamilyIntrinsicDifferentials318.omega p,j ''ᵁ ⊤)) :
    (frame j p h e).hom.app ⊤
      (IntrinsicTensorSheaf318.pure (FamilyIntrinsicDifferentials318.omega p)
        (FamilyIntrinsicDifferentials318.omega p) (j ''ᵁ ⊤) m n) =
    (show Γ(Spec (CommRingCat.of S),⊤) from (IntrinsicFrameDerivative318.chartFrame j p h e).hom.app ⊤ m)*
      (show Γ(Spec (CommRingCat.of S),⊤) from (IntrinsicFrameDerivative318.chartFrame j p h e).hom.app ⊤ n) := by
  change TensorSheafFunctor318.unitIso.hom.app ⊤
    ((TensorSheafFunctor318.congr (IntrinsicFrameDerivative318.chartFrame j p h e)
      (IntrinsicFrameDerivative318.chartFrame j p h e)).hom.app ⊤
      ((TensorOpenRestriction318.iso j (FamilyIntrinsicDifferentials318.omega p)
        (FamilyIntrinsicDifferentials318.omega p)).hom.app ⊤
        (IntrinsicTensorSheaf318.pure _ _ _ m n))) = _
  rw [TensorSheafNormalization318.restriction_pure,
    TensorSheafNormalization318.congr_pure,TensorSheafNormalization318.unitIso_pure]

@[expose] def basis (s : S) :=
  IntrinsicTensorSheaf318.pure (FamilyIntrinsicDifferentials318.omega p)
    (FamilyIntrinsicDifferentials318.omega p) (j ''ᵁ ⊤)
    (IntrinsicChartSections318.sectionMap j p h (KaehlerDifferential.D R S s))
    (IntrinsicChartSections318.sectionMap j p h (KaehlerDifferential.D R S s))

theorem basis_normalized (s : S) (hs : e (KaehlerDifferential.D R S s)=1) :
    (frame j p h e).hom.app ⊤ (basis j p h s)=
      (show Γ(Spec (CommRingCat.of S),⊤) from 1) := by
  change (frame j p h e).hom.app ⊤ (IntrinsicTensorSheaf318.pure _ _ _ _ _) = _
  rw [frame_pure,IntrinsicFrameDerivative318.chartFrame_section j p h e s hs,mul_one]

@[expose] def ambientFrame :
    (Scheme.Modules.restrictFunctor j).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
    (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
      (FamilyIntrinsicDifferentials318.omega p)).restrict j :=
  Scheme.Modules.restrictUnitIso j ≪≫ (frame j p h e).symm

theorem ambientFrame_one (s : S) (hs : e (KaehlerDifferential.D R S s)=1) :
    (ambientFrame j p h e).hom.val.app (op ⊤) (show Γ(Y,j ''ᵁ ⊤) from 1)=basis j p h s := by
  have hunit : (Scheme.Modules.restrictUnitIso j).hom.app ⊤
      (show Γ(Y,j ''ᵁ ⊤) from 1)=(show Γ(Spec (CommRingCat.of S),⊤) from 1) := by
    change (j.appIso ⊤).hom.hom 1=1
    exact map_one _
  change (frame j p h e).inv.app ⊤
    ((Scheme.Modules.restrictUnitIso j).hom.app ⊤ (show Γ(Y,j ''ᵁ ⊤) from 1))=_
  rw [hunit]
  apply (ConcreteCategory.bijective_of_isIso ((frame j p h e).hom.app ⊤)).1
  exact (congrArg (fun f => f.app ⊤ (show Γ(Spec (CommRingCat.of S),⊤) from 1))
    (frame j p h e).inv_hom_id).trans (basis_normalized j p h e s hs).symm

theorem generator_bijective (s : S) (hs : e (KaehlerDifferential.D R S s)=1)
    (V : Y.Opens) (hV : V ≤ j ''ᵁ ⊤) :
    Function.Bijective (fun a : Γ(Y,V) => a •
      (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
        (FamilyIntrinsicDifferentials318.omega p)).presheaf.map (homOfLE hV).op (basis j p h s)) :=
  RestrictedFrameLocal318.generator_bijective j _ (ambientFrame j p h e)
    (basis j p h s) (ambientFrame_one j p h e s hs) V hV

/-- A regular unit coefficient preserves generation on every subopen of the
actual chart image, not only on its generic fiber. -/
theorem weighted_generator_bijective (s a : S) (hs : e (KaehlerDifferential.D R S s)=1)
    (ha : IsUnit a) (V : Y.Opens) (hV : V ≤ j ''ᵁ ⊤) :
    Function.Bijective (fun r : Γ(Y,V) => r •
      (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
        (FamilyIntrinsicDifferentials318.omega p)).presheaf.map (homOfLE hV).op
        (IntrinsicTensorChartSections318.weightedSquare j p h a (KaehlerDifferential.D R S s))) := by
  let a0 : Γ(Y,j ''ᵁ ⊤) := (j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of S)).inv a)
  let av : Γ(Y,V) := Y.presheaf.map (homOfLE hV).op a0
  have hav : IsUnit av := ((ha.map (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom).map
    (j.appIso ⊤).inv.hom).map (Y.presheaf.map (homOfLE hV).op).hom
  have hb := (generator_bijective j p h e s hs V hV).comp (IsUnit.isUnit_iff_mulRight_bijective.mp hav)
  have heq : (fun r : Γ(Y,V) => r •
      (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
        (FamilyIntrinsicDifferentials318.omega p)).presheaf.map (homOfLE hV).op
        (IntrinsicTensorChartSections318.weightedSquare j p h a (KaehlerDifferential.D R S s))) =
    (fun r : Γ(Y,V) => r •
      (IntrinsicTensorSheaf318.tensor (FamilyIntrinsicDifferentials318.omega p)
        (FamilyIntrinsicDifferentials318.omega p)).presheaf.map (homOfLE hV).op (basis j p h s)) ∘
      (fun r : Γ(Y,V) => r*av) := by
    funext r
    change r • _ = (r*av) • _
    rw [IntrinsicTensorChartSections318.weightedSquare,Scheme.Modules.map_smul,smul_smul]
    rfl
  rw [heq]
  exact hb
end IntrinsicTensorGenerator318
