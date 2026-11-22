module

public import SelectedSameAIntrinsicPullbackSquare318
public import SelectedSameAFibreAffineProjection318
public import IntrinsicChartNormalization318

/-!
# Restrict the genuine old-family differential map to its actual affine

The first map of the original cotangent transitivity row is identified
before fibre pullback, preserving its true derivative on the old base.
-/

public section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct ModuleCat.Algebra

namespace SelectedSameAOldAffineJacobian318

universe u
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false


local notation "F" => Scheme.Modules.pullback
local notation "PB" => IntrinsicDifferentialPullback318.pullbackMap
local notation "Ω" => FamilyIntrinsicDifferentials318.omega

section OpenRestriction

variable {Y U T : Scheme.{u}} {K : CommRingCat.{u}}
variable (p : Y ⟶ T) (j : U ⟶ Y) [IsOpenImmersion j] (r : U ⟶ T)
variable (h : j ≫ p = r) (b : T ⟶ Spec K)

@[expose] def chartSourceComparison :
    ((F p).obj (Ω b)).restrict j ≅ (F r).obj (Ω b) :=
  (Scheme.Modules.restrictFunctorIsoPullback j).app _ ≪≫
    (Scheme.Modules.pullbackComp j p).app _ ≪≫ (Scheme.Modules.pullbackCongr h).app _

/-- On the actual open, the restricted relative map is precisely the
intrinsic pullback for its structural morphism, with the real base
triangle used for its target normalization. -/
theorem actual_restriction (q : Y ⟶ Spec K) (t : U ⟶ Spec K)
    (hp : p ≫ b = q) (hj : j ≫ q = t) (hr : r ≫ b = t) :
    let d : FamilyRestrictionNormalization318.Data j
        (FamilyIntrinsicDifferentials318.coefficients q)
        (FamilyIntrinsicDifferentials318.coefficients t) :=
      congrArg FamilyIntrinsicDifferentials318.coefficients hj ▸
        FamilyRestrictionNormalization318.familyData j q
    (Scheme.Modules.restrictFunctor j).map (PB p q b hp) ≫ d.iso.hom =
      (chartSourceComparison p j r h b).hom ≫ PB r t b hr := by
  subst r
  subst t
  change (Scheme.Modules.restrictFunctor j).map (PB p q b hp) ≫
      (FamilyRestrictionNormalization318.iso j q).hom = _
  rw [← SelectedSameAIntrinsicPullbackSquare318.open_normalized j q,
    ← Category.assoc,
    (Scheme.Modules.restrictFunctorIsoPullback j).hom.naturality (PB p q b hp),
    Category.assoc]
  have hComp := SelectedSameAIntrinsicPullbackSquare318.pullback_comp j p (j ≫ q) q b rfl hp hr
  have hComp' : (F j).map (PB p q b hp) ≫ PB j (j ≫ q) q rfl =
    (Scheme.Modules.pullbackComp j p).hom.app (Ω b) ≫ PB (j ≫ p) (j ≫ q) b hr := by
    rw [← hComp, Iso.hom_inv_id_app_assoc]
  rw [hComp']
  simp only [chartSourceComparison, Scheme.Modules.pullbackCongr, eqToIso_refl,
    Iso.refl_hom, NatTrans.id_app, Iso.trans_hom, Iso.app_hom, Category.assoc, Category.id_comp]

end OpenRestriction

variable {k T C : Type u} [CommRing k] [CommRing T] [CommRing C]
  [Algebra k T] [Algebra k C] [Algebra T C] [IsScalarTower k T C]
variable {Y : Scheme.{u}} (p : Y ⟶ (Spec (CommRingCat.of T))) (j : (Spec (CommRingCat.of C)) ⟶ Y) [IsOpenImmersion j]
variable (q : Y ⟶ (Spec (CommRingCat.of k))) (hp : p ≫ Spec.algebraMap k T = q)
variable (h : j ≫ p = Spec.algebraMap T C) (hj : j ≫ q = Spec.algebraMap k C)

/-- Actual source coordinates for the old base-to-total pulled map. -/
@[expose] def affineOldSource :
    ((F p).obj (Ω (Spec.algebraMap k T))).restrict j ≅
      tilde (R := CommRingCat.of C) (ModuleCat.of C (C ⊗[T] KaehlerDifferential k T)) :=
  chartSourceComparison p j _ h (Spec.algebraMap k T) ≪≫
    (F (Spec.algebraMap T C)).mapIso
      (AffineIntrinsicNormalization318.algebraIso (R := k) (S := T)).symm ≪≫
    SelectedSameAFibreAffineProjection318.tensorIso k T C

/-- On the actual affine, the first map of old transitivity is exactly the
genuine Kähler base-to-absolute linear map, before any closed-fibre pull. -/
theorem actual_old_jacobian :
    (Scheme.Modules.restrictFunctor j).map (PB p q (Spec.algebraMap k T) hp) ≫
      (IntrinsicChartNormalization318.iso j q hj).inv =
    (affineOldSource p j h).hom ≫ (tilde.functor (CommRingCat.of C)).map
      (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k T C)) := by
  let r := Spec.algebraMap T C
  let b := Spec.algebraMap k T
  let t := Spec.algebraMap k C
  let I := (AffineIntrinsicNormalization318.algebraIso (R := k) (S := T))
  let J := (AffineIntrinsicNormalization318.algebraIso (R := k) (S := C))
  let hrt : r ≫ b = t := SelectedSameAFibreAffineProjection318.over_comp k T C
  let E := chartSourceComparison p j r h b
  let d := (IntrinsicChartNormalization318.restrictionData j q hj).iso
  have hs := actual_restriction p j r h b q t hp hj hrt
  change (Scheme.Modules.restrictFunctor j).map (PB p q b hp) ≫ d.hom =
    E.hom ≫ PB r t b hrt at hs
  have hx : (F r).map I.hom ≫ PB r t b hrt =
      SelectedSameAFibreAffineProjection318.right k T C ≫ J.hom :=
    SelectedSameAFibreAffineProjection318.affine_intrinsic_right k T C
  have hy : PB r t b hrt ≫ J.inv =
      (F r).map I.inv ≫ SelectedSameAFibreAffineProjection318.right k T C := by
    calc
      _ = (F r).map I.inv ≫ ((F r).map I.hom ≫ PB r t b hrt) ≫ J.inv := by
        simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id,
          Category.id_comp]
      _ = _ := by rw [hx]; simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [IntrinsicChartNormalization318.iso, affineOldSource,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom, Category.assoc]
  change (Scheme.Modules.restrictFunctor j).map (PB p q b hp) ≫ d.hom ≫ J.inv =
    E.hom ≫ (F r).map I.inv ≫ (SelectedSameAFibreAffineProjection318.tensorIso k T C).hom
      ≫ (tilde.functor (CommRingCat.of C)).map (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k T C))
  rw [← Category.assoc ((Scheme.Modules.restrictFunctor j).map _) d.hom J.inv, hs]
  simp only [Category.assoc, hy]
  rw [← SelectedSameAFibreAffineProjection318.right_on_tensor k T C]

end SelectedSameAOldAffineJacobian318
