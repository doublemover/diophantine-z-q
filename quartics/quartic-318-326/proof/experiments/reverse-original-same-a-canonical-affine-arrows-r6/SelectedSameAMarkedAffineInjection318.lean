module

public import SelectedSameAActualAffineMiddle318
public import SelectedSameAUnitOpenSquare318
public import SelectedSameAAffinePulledUnitBeta318
import all SelectedSameAActualFibreSheafArrows318

/-!
# The actual left arrow on the same closed-fibre affine chart

The left arrow is the shear-free section corresponding to the actual
generator 1 tensor d epsilon, not a scalar multiple in an unspecified
chart frame. All chart maps are the same maps used for the right arrow.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings ModuleCat.Algebra

namespace SelectedSameAMarkedAffineInjection318

universe u
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open SelectedSameAActualFibreSheafArrows318
open SelectedSameAActualAffineMiddle318

variable {k C B : Type u} [CommRing k] [CommRing C] [CommRing B]
  [Algebra k C] [Algebra k B] [Algebra C B] [IsScalarTower k C B]
  [Algebra (D k) C]
variable {X A : Scheme.{u}} (σ : X ⟶ spec (D k)) (ρ : A ⟶ X)
variable (j : spec C ⟶ X) (l : spec B ⟶ A) [IsOpenImmersion j] [IsOpenImmersion l]
variable (hσ : j ≫ σ = sMap (algebraMap (D k) C))
variable (hsq : l ≫ ρ = sMap (algebraMap C B) ≫ j)
variable (hj : j ≫ xOverK σ = sMap (algebraMap k C))


include hσ

private theorem eps_on_chart :
    j.appTop (epsilonSection σ) = (Scheme.ΓSpecIso (CommRingCat.of C)).inv (algebraMap (D k) C (eps k)) := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of (D k))).inv ≫ σ.appTop ≫ j.appTop =
      CommRingCat.ofHom (algebraMap (D k) C) ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).inv := by
    rw [← Scheme.Hom.comp_appTop, hσ, Scheme.ΓSpecIso_inv_naturality]
  exact congrArg (fun f => f (eps k)) h

/-- On the original affine upstairs chart the restricted global section is
the intrinsic image of the differential of the actual epsilon coefficient. -/
theorem local_raw_left :
    LocalCoordinateRelation318.localMap j (rawLeft σ) =
      ModuleGlobalSections318.ofTop (tilde (R := CommRingCat.of C) (ModuleCat.of C (KaehlerDifferential k C)))
        ((tilde.isoTop (R := CommRingCat.of C) (ModuleCat.of C (KaehlerDifferential k C))).hom (KaehlerDifferential.D k C (algebraMap (D k) C (eps k)))) ≫ (IntrinsicChartNormalization318.iso j (xOverK σ) hj).hom := by
  apply ModuleTopExt318.ext
  rw [LocalCoordinateRelation318.localMap_top_one]
  change (omegaX σ).presheaf.map
    (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op
      ((rawLeft σ).val.app (op ⊤) (show Γ(X, ⊤) from 1)) =
    (moduleSpecΓFunctor.map (IntrinsicChartNormalization318.iso j (xOverK σ) hj).hom)
      ((ModuleGlobalSections318.ofTop (tilde (R := CommRingCat.of C) (ModuleCat.of C (KaehlerDifferential k C))) _).val.app
        (op ⊤) (show Γ(spec C, ⊤) from 1))
  unfold rawLeft
  rw [ModuleTopMorphisms318.ofTop_top_one, ModuleTopMorphisms318.ofTop_top_one,
    IntrinsicChartNormalization318.differential]
  let i := (homOfLE (show j ''ᵁ ⊤ ≤ ⊤ from le_top)).op
  have hres :=
    ((FamilyIntrinsicDifferentials318.D (xOverK σ)).d_map i (epsilonSection σ)).symm
  change (omegaX σ).presheaf.map i
      ((FamilyIntrinsicDifferentials318.D (xOverK σ)).d (epsilonSection σ)) =
    (FamilyIntrinsicDifferentials318.D (xOverK σ)).d (X := op (j ''ᵁ ⊤))
      (X.presheaf.map i (epsilonSection σ)) at hres
  refine hres.trans ?_
  have hc := congrArg (fun f => f (epsilonSection σ)) (j.app_appIso_inv ⊤)
  exact congrArg
    ((FamilyIntrinsicDifferentials318.D (xOverK σ)).d (X := op (j ''ᵁ ⊤)))
    (hc.symm.trans (congrArg (fun x => (j.appIso ⊤).inv x) (eps_on_chart σ j hσ)))

/-- Canonical left-arrow generator, expressed as an actual sheaf-module
map over the literal reduction chart. -/
theorem left_on_chart :
    (sourceOnChart l).inv ≫ (Scheme.Modules.restrictFunctor l).map (left σ ρ) ≫
      (middleOnChart σ ρ j l hsq hj).hom =
    ModuleGlobalSections318.ofTop (tilde (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[C] KaehlerDifferential k C)))
      ((tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[C] KaehlerDifferential k C))).hom ((1 : B) ⊗ₜ[C] KaehlerDifferential.D k C (algebraMap (D k) C (eps k)))) := by
  let r := CommRingCat.ofHom (algebraMap C B)
  let F := Scheme.Modules.pullback (Spec.map r)
  let α := (ScalarExtensionTensor318.tensorEquiv (T := B) (ModuleCat.of C (KaehlerDifferential k C))).toModuleIso.hom
  let b := KaehlerDifferential.D k C (algebraMap (D k) C (eps k))
  let t := ModuleGlobalSections318.ofTop (tilde (R := CommRingCat.of C) (ModuleCat.of C (KaehlerDifferential k C)))
    ((tilde.isoTop (R := CommRingCat.of C) (ModuleCat.of C (KaehlerDifferential k C))).hom b)
  have hs := SelectedSameAUnitOpenSquare318.restrict_pulled_section ρ j l (Spec.map r) hsq
    (rawLeft σ)
  rw [local_raw_left σ j hσ hj] at hs
  change _ = PulledCoordinateMaps318.map (Spec.map r) (t ≫ (IntrinsicChartNormalization318.iso j (xOverK σ) hj).hom) at hs
  have ht := SelectedSameAAffinePulledUnitBeta318.pull_ofTop r (ModuleCat.of C (KaehlerDifferential k C)) b
  simp only [sourceOnChart, middleOnChart, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
    Functor.mapIso_hom, Category.assoc]
  change (Scheme.Modules.restrictUnitIso l).inv ≫
    (Scheme.Modules.restrictFunctor l).map (PulledCoordinateMaps318.map ρ (rawLeft σ)) ≫
    (PullbackLineFrames318.chartIso ρ j l (Spec.map r) hsq (omegaX σ)).hom ≫
    F.map (IntrinsicChartNormalization318.iso j (xOverK σ) hj).inv ≫ (SelectedSameAFibreAffineProjection318.tensorIso k C B).hom = _
  rw [← Category.assoc ((Scheme.Modules.restrictFunctor l).map _) _ _,
    ← Category.assoc (Scheme.Modules.restrictUnitIso l).inv,
    ← show (PullbackChartNaturality318.chartNatIso ρ j l (Spec.map r) hsq).hom.app (omegaX σ) =
        (PullbackLineFrames318.chartIso ρ j l (Spec.map r) hsq (omegaX σ)).hom from
          congrArg Iso.hom (PullbackChartNaturality318.app_eq ρ j l (Spec.map r) hsq (omegaX σ)), hs]
  let E := IntrinsicChartNormalization318.iso j (xOverK σ) hj
  let p := (SelectedSameAFibreAffineProjection318.tensorIso k C B).hom
  have hi : F.map E.hom ≫ F.map E.inv = 𝟙 _ :=
    ((F.map_comp E.hom E.inv).symm.trans
      (congrArg (fun f => F.map f) E.hom_inv_id)).trans (F.map_id _)
  have hip : F.map E.hom ≫ F.map E.inv ≫ p = p := by
    rw [← Category.assoc, hi, Category.id_comp]
  have hcomp : F.map (t ≫ E.hom) ≫ F.map E.inv ≫ p = F.map t ≫ p := by
    simp only [F.map_comp, Category.assoc, hip]
  change (IdentityCotangent318.pullbackUnitIso (Spec.map r)).inv ≫
    (F.map (t ≫ E.hom) ≫ F.map E.inv ≫ p) = _
  rw [hcomp]
  change PulledCoordinateMaps318.map (Spec.map r) t ≫
    (SelectedSameAFibreAffineProjection318.tensorIso k C B).hom = _
  simp only [SelectedSameAFibreAffineProjection318.tensorIso, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom]
  rw [← Category.assoc, ht, ModuleTopMorphisms318.ofTop_comp]
  have hn := (tilde.toTildeΓNatIso (R := CommRingCat.of B)).hom.naturality α
  have hv := congrArg (fun f => f ((1 : B) ⊗ₜ[C, algebraMap C B] b)) hn
  change (tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[C] KaehlerDifferential k C))).hom
      (α ((1 : B) ⊗ₜ[C, algebraMap C B] b)) =
    ((tilde.functor (CommRingCat.of B)).map α).app ⊤
      ((tilde.isoTop (R := CommRingCat.of B) _).hom ((1 : B) ⊗ₜ[C, algebraMap C B] b)) at hv
  rw [← hv]
  change _ = ModuleGlobalSections318.ofTop (tilde (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[C] KaehlerDifferential k C)))
    ((tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[C] KaehlerDifferential k C))).hom ((1 : B) ⊗ₜ[C] b))
  change ModuleGlobalSections318.ofTop (tilde (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[C] KaehlerDifferential k C)))
    ((tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[C] KaehlerDifferential k C))).hom
      (ScalarExtensionTensor318.tensorEquiv (T := B) (ModuleCat.of C (KaehlerDifferential k C)) ((1 : B) ⊗ₜ[C, algebraMap C B] b))) = _
  rw [ScalarExtensionTensor318.tensorEquiv_tmul]

end SelectedSameAMarkedAffineInjection318
