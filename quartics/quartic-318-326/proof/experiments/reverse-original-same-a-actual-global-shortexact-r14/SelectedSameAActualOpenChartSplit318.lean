module

public import SelectedSameAMarkedAffineInjection318
public import SelectedSameAActualAffineKSSequence318
public import SelectedSameAModuleSplitExplicit318
public import SelectedActualAdditiveStalkLocalExact318
public import UnitLineDifferentials318
import all SelectedSameAActualFibreSheafArrows318
import all SelectedSameAActualAffineKSSequence318
import all SelectedSameADualNumberFlatCoefficient318

/-!
# Split the restriction of the actual directional cotangent complex

Neither the normalized affine row nor the three sheaf isomorphisms
are assumed here. They are constructed from the actual diagram.
-/

public section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct ModuleCat.Algebra

namespace SelectedSameAActualOpenChartSplit318

universe u
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open SelectedSameAActualFibreSheafArrows318
open SelectedSameAActualAffineMiddle318
open SelectedSameAActualAffineKSSequence318
open SelectedSameADualNumberFlatCoefficient318

variable {k C B : Type u} [CommRing k] [CommRing C] [CommRing B]
  [Algebra k C] [Algebra k B] [Algebra C B] [IsScalarTower k C B]
  [Algebra (D k) C]

/-- The true affine d-epsilon map at the genuine unit agrees with its
linear-module tilde definition, with the specified tilde-self comparison. -/
theorem tilde_left_at_actual_unit :
    (tildeSelf (R := CommRingCat.of B)).inv ≫
      (tilde.functor (CommRingCat.of B)).map (ModuleCat.ofHom (ι k C B)) =
    ModuleGlobalSections318.ofTop (tilde (R := CommRingCat.of B) (ModuleCat.of B (E k C B)))
      ((tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B (E k C B))).hom (dEps k C B)) := by
  apply ModuleTopExt318.ext
  let M := tilde (R := CommRingCat.of B) (ModuleCat.of B (E k C B))
  let z : Γ(M,⊤) :=
    (tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B (E k C B))).hom (dEps k C B)
  have hRight : (ModuleGlobalSections318.ofTop M z).val.app (op ⊤)
      (show Γ(spec B, ⊤) from 1) = z :=
    ModuleTopMorphisms318.ofTop_top_one z
  refine Eq.trans ?_ hRight.symm
  let e := ModuleCat.ofHom (ι k C B)
  have hu : (tildeSelf (R := CommRingCat.of B)).inv.app ⊤
      (show Γ(spec B, ⊤) from 1) =
      (tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B B)).hom (1 : B) := by
    rw [UnitLineDifferentials318.isoTop_one]
    simp only [tildeSelf, Iso.refl_inv]
    let L : (spec B).Modules := tilde (R := CommRingCat.of B) (ModuleCat.of B B)
    let x : Γ(L, ⊤) := (show Γ(spec B, ⊤) from 1)
    have hid := Scheme.Modules.Hom.id_app (U := (⊤ : (spec B).Opens)) L
    have he := congrArg (fun f : Γ(L, ⊤) ⟶ Γ(L, ⊤) => f x) hid
    simpa only [L, x, ConcreteCategory.id_apply] using he
  have he := (tilde.toTildeΓNatIso (R := CommRingCat.of B)).hom.naturality e
  have hv := congrArg (fun q => q (1 : B)) he
  change (tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B (E k C B))).hom
      (ι k C B (1 : B)) =
    ((tilde.functor (CommRingCat.of B)).map e).app ⊤
      ((tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B B)).hom (1 : B)) at hv
  change ((tilde.functor (CommRingCat.of B)).map e).app ⊤
    ((tildeSelf (R := CommRingCat.of B)).inv.app ⊤ (show Γ(spec B, ⊤) from 1)) = _
  calc
    _ = ((tilde.functor (CommRingCat.of B)).map e).app ⊤
        ((tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B B)).hom (1 : B)) :=
      congrArg (fun w => ((tilde.functor (CommRingCat.of B)).map e).app ⊤ w) hu
    _ = (tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B (E k C B))).hom
        (ι k C B (1 : B)) := hv.symm
    _ = z := by
      change (tilde.isoTop (R := CommRingCat.of B) (ModuleCat.of B (E k C B))).hom
        ((1 : B) • dEps k C B) = z
      rw [one_smul] <;> rfl

variable [hFlat : Module.Flat (D k) C]

include hFlat in
private theorem actual_retract_exists
    (ρr : C →ₐ[k] B) (s : B →ₐ[k] C) (hs : ∀ b, ρr (s b) = b)
    (hρr : algebraMap C B = ρr.toRingHom)
    (hk : RingHom.ker (algebraMap C B) = Ideal.span ({epsilonIn k C} : Set C)) :
    ∃ r : E k C B →ₗ[B] B, Function.LeftInverse r (ι k C B) := by
  have hk' : RingHom.ker ρr.toRingHom = Ideal.span ({epsilonIn k C} : Set C) := by rw [← hρr, hk]
  let ν := SelectedSameACechEpsilonReadout318.coefficientDerivation k C B ρr s hs hk' hρr
  let r : E k C B →ₗ[B] B := ν.liftKaehlerDifferential.liftBaseChange B
  have hr : r (dEps k C B) = 1 := by
    change ν.liftKaehlerDifferential.liftBaseChange B
      ((1 : B) ⊗ₜ[C] KaehlerDifferential.D k C (epsilonIn k C)) = 1
    rw [LinearMap.liftBaseChange_tmul, one_smul, Derivation.liftKaehlerDifferential_comp_D]
    exact SelectedSameACechEpsilonReadout318.coefficient_on_epsilon k C B ρr s hs hk'
  refine ⟨r, ?_⟩
  intro b
  change r (b • dEps k C B) = b
  rw [LinearMap.map_smul, hr, smul_eq_mul, mul_one]

section Chart
variable {X A : Scheme.{u}} (σ : X ⟶ spec (D k)) (ρ : A ⟶ X) (a : A ⟶ spec k)
variable (h : ρ ≫ σ = a ≫ sMap (pr k))
variable (j : spec C ⟶ X) (l : spec B ⟶ A) [IsOpenImmersion j] [IsOpenImmersion l]
variable (hσ : j ≫ σ = sMap (algebraMap (D k) C))
variable (hsq : l ≫ ρ = sMap (algebraMap C B) ≫ j)
variable (hj : j ≫ xOverK σ = sMap (algebraMap k C))
variable (hl : l ≫ a = sMap (algebraMap k B))

variable [hSmooth : Algebra.FormallySmooth k B]
variable (ρr : C →ₐ[k] B) (hρr : algebraMap C B = ρr.toRingHom)
variable (hk : RingHom.ker (algebraMap C B) = Ideal.span ({epsilonIn k C} : Set C))
variable (hSurjC : Function.Surjective (algebraMap C B))

include hFlat hSmooth hσ hsq hj hl ρr hρr hk hSurjC in
/-- The only flatness here is over the dual-number deformation base.
The marked closed-fibre affine reduction itself need not be flat. -/
theorem actual_open_chart_split :
    Nonempty (((moduleComplex σ ρ a h).map (Scheme.Modules.restrictFunctor l)).Splitting) := by
  have hSurjR : Function.Surjective ρr := by
    have H := hSurjC
    rw [hρr] at H
    exact H
  have hk' : RingHom.ker ρr.toRingHom = Ideal.span ({epsilonIn k C} : Set C) := by rw [← hρr, hk]
  let s := SelectedSameAADualNumberAffineChart318.chosenSection k C B ρr hSurjR hk'
  have hs : ∀ b, ρr (s b) = b :=
    SelectedSameAADualNumberAffineChart318.chosenSection_reduce k C B ρr hSurjR hk'
  obtain ⟨hSurj, hExact⟩ := exact_at_middle k C B hk hSurjC
  obtain ⟨r, hr⟩ := actual_retract_exists ρr s hs hρr hk
  letI : (tilde.functor (CommRingCat.of B)).Additive := by
    constructor
    intro M N f g
    exact AlgebraicGeometry.tilde.map_add f g
  letI : (tilde.functor (CommRingCat.of B)).PreservesZeroMorphisms :=
    Functor.preservesZeroMorphisms_of_additive (tilde.functor (CommRingCat.of B))
  let R := SelectedSameAModuleSplitExplicit318.row (ι k C B) (π k C B) hExact
  have e : ((moduleComplex σ ρ a h).map (Scheme.Modules.restrictFunctor l)) ≅
      R.map (tilde.functor (CommRingCat.of B)) := by
    refine ShortComplex.isoMk ((sourceOnChart l) ≪≫ (tildeSelf (R := CommRingCat.of B)).symm)
      (middleOnChart σ ρ j l hsq hj) (targetOnChart a l hl) ?_ ?_
    · apply (cancel_epi (sourceOnChart l).inv).mp
      change (sourceOnChart l).inv ≫
        (((sourceOnChart l) ≪≫ (tildeSelf (R := CommRingCat.of B)).symm).hom ≫
          (tilde.functor (CommRingCat.of B)).map (ModuleCat.ofHom (ι k C B))) =
        (sourceOnChart l).inv ≫ (Scheme.Modules.restrictFunctor l).map (left σ ρ) ≫
          (middleOnChart σ ρ j l hsq hj).hom
      simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
      rw [SelectedSameAMarkedAffineInjection318.left_on_chart σ ρ j l hσ hsq hj]
      exact tilde_left_at_actual_unit (k := k) (C := C) (B := B)
    · exact (right_on_chart σ ρ a j l hsq hj hl h).symm
  let b := SelectedSameAModuleSplitExplicit318.splitting (ι k C B) (π k C B) hExact r hr hSurj
  exact ⟨(b.map (tilde.functor (CommRingCat.of B))).ofIso e.symm⟩

end Chart

end SelectedSameAActualOpenChartSplit318
