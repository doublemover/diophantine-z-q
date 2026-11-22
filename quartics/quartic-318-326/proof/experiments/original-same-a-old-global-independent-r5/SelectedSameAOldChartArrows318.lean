module

public import SelectedSameAOldAffineJacobian318
public import SelectedSameAActualTildeTensorNaturality318
public import SelectedSameAOldCotangentFibreSplit318
public import PullbackChartNaturality318

/-!
# Actual old-family differential arrows on their actual fibre chart

The old left remains i*dp. It is compared via actual naturality of
pullbacks and ordered tensor cancellation, not by selecting a basis of it.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace SelectedSameAOldChartArrows318

universe u
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open SelectedSameAOldAffineJacobian318

local notation "F" => Scheme.Modules.pullback
local notation "PB" => IntrinsicDifferentialPullback318.pullbackMap
local notation "Ω" => FamilyIntrinsicDifferentials318.omega
local notation "res" => Scheme.Modules.restrictFunctor

variable {k T C B : Type u} [CommRing k] [CommRing T] [CommRing C] [CommRing B]
  [Algebra k T] [Algebra k C] [Algebra k B] [Algebra T C] [Algebra C B] [Algebra T B]
  [IsScalarTower k T C] [IsScalarTower k C B] [IsScalarTower T C B]
variable {P A : Scheme.{u}} (p : P ⟶ (Spec (CommRingCat.of T))) (q : P ⟶ (Spec (CommRingCat.of k))) (a : A ⟶ (Spec (CommRingCat.of k))) (i : A ⟶ P)
variable (j : (Spec (CommRingCat.of C)) ⟶ P) (l : (Spec (CommRingCat.of B)) ⟶ A) [IsOpenImmersion j] [IsOpenImmersion l]
variable (hp : p ≫ Spec.algebraMap k T = q) (hi : i ≫ q = a)
variable (hj : j ≫ q = Spec.algebraMap k C) (hl : l ≫ a = Spec.algebraMap k B)
variable (hs : j ≫ p = Spec.algebraMap T C) (hr : l ≫ i = Spec.algebraMap C B ≫ j)

@[expose] def oldMiddle :
    ((F i).obj (Ω q)).restrict l ≅
      tilde (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[C] KaehlerDifferential k C)) :=
  PullbackLineFrames318.chartIso i j l _ hr (Ω q) ≪≫
    (F (Spec.algebraMap C B)).mapIso (IntrinsicChartNormalization318.iso j q hj).symm ≪≫
    SelectedSameAFibreAffineProjection318.tensorIso k C B

@[expose] def oldTarget :
    (Ω a).restrict l ≅ tilde (R := CommRingCat.of B) (ModuleCat.of B (KaehlerDifferential k B)) :=
  (IntrinsicChartNormalization318.iso l a hl).symm

/-- First re-associate the literal pullbacks; finally contract the units
of the actual intermediate total-space algebra. -/
@[expose] def oldSource :
    ((F i).obj ((F p).obj (Ω (Spec.algebraMap k T)))).restrict l ≅
      tilde (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[T] KaehlerDifferential k T)) :=
  PullbackLineFrames318.chartIso i j l _ hr ((F p).obj (Ω (Spec.algebraMap k T))) ≪≫
    (F (Spec.algebraMap C B)).mapIso (affineOldSource p j hs) ≪≫
    SelectedSameAActualTildeTensorNaturality318.tensorIso C B
      (ModuleCat.of C (C ⊗[T] KaehlerDifferential k T)) ≪≫
    (tilde.functor (CommRingCat.of B)).mapIso
      (TensorProduct.AlgebraTensorModule.cancelBaseChange T C B B (KaehlerDifferential k T)).toModuleIso

theorem old_right_normalized :
    (res l).map (PB i a q hi) ≫ (oldTarget a l hl).hom =
      (oldMiddle q i j l hj hr).hom ≫ (tilde.functor (CommRingCat.of B)).map
        (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k C B)) := by
  let r := Spec.algebraMap C B
  let dc := (IntrinsicChartNormalization318.restrictionData j q hj).iso
  let db := (IntrinsicChartNormalization318.restrictionData l a hl).iso
  let I := AffineIntrinsicNormalization318.algebraIso (R := k) (S := C)
  let J := AffineIntrinsicNormalization318.algebraIso (R := k) (S := B)
  let E := PullbackLineFrames318.chartIso i j l r hr (Ω q)
  let ht : r ≫ Spec.algebraMap k C = Spec.algebraMap k B :=
    SelectedSameAFibreAffineProjection318.over_comp k C B
  let m := PB r (Spec.algebraMap k B) (Spec.algebraMap k C) ht
  have h0 := SelectedSameAIntrinsicPullbackSquare318.actual_open_square_rebased
    i a q hi j l r hr (Spec.algebraMap k C) (Spec.algebraMap k B) hj hl ht
  change (res l).map (PB i a q hi) ≫ db.hom = E.hom ≫ (F r).map dc.hom ≫ m at h0
  have h1 : (F r).map I.hom ≫ m = SelectedSameAFibreAffineProjection318.right k C B ≫ J.hom :=
    SelectedSameAFibreAffineProjection318.affine_intrinsic_right k C B
  have h2 : m ≫ J.inv = (F r).map I.inv ≫ SelectedSameAFibreAffineProjection318.right k C B := by
    calc
      _ = (F r).map I.inv ≫ ((F r).map I.hom ≫ m) ≫ J.inv := by
        simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.id_comp]
      _ = _ := by rw [h1]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [oldTarget, oldMiddle, IntrinsicChartNormalization318.iso, Iso.trans_hom,
    Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Category.assoc]
  change (res l).map (PB i a q hi) ≫ db.hom ≫ J.inv =
    E.hom ≫ (F r).map (dc.hom ≫ I.inv) ≫
      (SelectedSameAFibreAffineProjection318.tensorIso k C B).hom ≫
      (tilde.functor (CommRingCat.of B)).map (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k C B))
  rw [← Category.assoc ((res l).map _) db.hom J.inv, h0]
  simp only [Category.assoc, h2, Functor.map_comp]
  rw [← SelectedSameAFibreAffineProjection318.right_on_tensor k C B]

-- Keep the genuine first map unexpanded until the actual chart naturality applies.
theorem old_left_normalized :
    (res l).map ((F i).map (PB p q (Spec.algebraMap k T) hp)) ≫ (oldMiddle q i j l hj hr).hom =
      (oldSource p i j l hs hr).hom ≫ (tilde.functor (CommRingCat.of B)).map
        (ModuleCat.ofHom (SelectedSameAOldCotangentFibreSplit318.leftOnFibre k T C B)) := by
  let r := Spec.algebraMap C B
  let d := PB p q (Spec.algebraMap k T) hp
  let M := ModuleCat.of C (C ⊗[T] KaehlerDifferential k T)
  let N := ModuleCat.of C (KaehlerDifferential k C)
  let e := ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k T C)
  let ψ := PullbackChartNaturality318.chartNatIso i j l r hr
  have hψ := ψ.hom.naturality d
  simp only [Functor.comp_map] at hψ
  have hN := SelectedSameAActualTildeTensorNaturality318.tensorIso_naturality C B e
  have hC := actual_old_jacobian p j q hp hs hj
  simp only [oldSource, oldMiddle, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [← PullbackChartNaturality318.app_eq i j l r hr,
    ← PullbackChartNaturality318.app_eq i j l r hr, ← Category.assoc ((res l).map _), hψ,
    Category.assoc, ← Functor.map_comp_assoc, hC, Functor.map_comp_assoc]
  change _ = _ ≫ (F r).map (affineOldSource p j hs).hom ≫
    (SelectedSameAActualTildeTensorNaturality318.tensorIso C B M).hom ≫
    (tilde.functor (CommRingCat.of B)).map
      (TensorProduct.AlgebraTensorModule.cancelBaseChange T C B B (KaehlerDifferential k T)).toModuleIso.hom ≫
    (tilde.functor (CommRingCat.of B)).map
      (ModuleCat.ofHom (SelectedSameAOldCotangentFibreSplit318.leftOnFibre k T C B))
  have ht :
      (SelectedSameAActualTildeTensorNaturality318.tensorIso C B N).hom =
        (SelectedSameAFibreAffineProjection318.tensorIso k C B).hom := rfl
  let tilB := tilde.functor (CommRingCat.of B)
  let cancel :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange T C B B (KaehlerDifferential k T)).toModuleIso
  let L := ModuleCat.ofHom
    (TensorProduct.AlgebraTensorModule.lTensor B B (KaehlerDifferential.mapBaseChange k T C))
  have hfac : ModuleCat.ofHom (SelectedSameAOldCotangentFibreSplit318.leftOnFibre k T C B) =
      cancel.inv ≫ L := by
    unfold SelectedSameAOldCotangentFibreSplit318.leftOnFibre
    exact ModuleCat.ofHom_comp _ _
  have hc : tilB.map cancel.hom ≫
      tilB.map (ModuleCat.ofHom (SelectedSameAOldCotangentFibreSplit318.leftOnFibre k T C B)) =
      tilB.map L := by
    calc
      _ = tilB.map cancel.hom ≫ tilB.map (cancel.inv ≫ L) :=
        congrArg (fun f => tilB.map cancel.hom ≫ tilB.map f) hfac
      _ = tilB.map (cancel.hom ≫ cancel.inv ≫ L) :=
        (tilB.map_comp cancel.hom (cancel.inv ≫ L)).symm
      _ = _ := congrArg (fun f => tilB.map f) (Iso.hom_inv_id_assoc cancel L)
  dsimp only [tilB, cancel, L] at hc
  rw [← ht]
  simp only [Category.assoc, hN, hc] <;> rfl

/-- The old two literal arrows are now present together on this one chart. -/
theorem old_affine_pair_ready :
    ((res l).map ((F i).map (PB p q (Spec.algebraMap k T) hp)) ≫ (oldMiddle q i j l hj hr).hom =
      (oldSource p i j l hs hr).hom ≫ (tilde.functor (CommRingCat.of B)).map
        (ModuleCat.ofHom (SelectedSameAOldCotangentFibreSplit318.leftOnFibre k T C B))) ∧
    ((res l).map (PB i a q hi) ≫ (oldTarget a l hl).hom =
      (oldMiddle q i j l hj hr).hom ≫ (tilde.functor (CommRingCat.of B)).map
        (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k C B))) :=
  ⟨old_left_normalized p q i j l hp hj hs hr, old_right_normalized q a i j l hi hj hl hr⟩

end

end SelectedSameAOldChartArrows318
