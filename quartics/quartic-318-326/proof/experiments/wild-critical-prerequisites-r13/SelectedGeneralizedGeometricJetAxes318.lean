module
public import SelectedGeneralizedGeometricIdentityJets318
public import Mathlib.LinearAlgebra.Prod
public section
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open SelectedGeneralizedAffineInfinity318 SelectedGeneralizedInfinityCartier318
open SelectedGeneralizedGluedCarrier318 SelectedGeneralizedInstallOriginOpen318
open SelectedGeneralizedGeometricIdentityJets318 SelectedGeneralizedInfinityActualJets318

namespace SelectedGeneralizedGeometricJetAxes318

universe u
variable {R : Type u} [CommRing R]

abbrev Points (d : Rˣ) {X : Scheme} (b : X ⟶ Base R) :=
  {q : X ⟶ Carrier d // q ≫ overBase d = b}

@[expose] def zeroPoint (d : Rˣ) {X : Scheme} (b : X ⟶ Base R) : Points d b :=
  ⟨b ≫ identitySection d, by rw [Category.assoc,identity_over,Category.comp_id]⟩

@[expose] def pair (d : Rˣ) {X : Scheme} {b : X ⟶ Base R} (p q : Points d b) :
    X ⟶ pullback (overBase d) (overBase d) :=
  pullback.lift p.val q.val (p.property.trans q.property.symm)

@[simp] theorem pair_fst (d : Rˣ) {X : Scheme} {b : X ⟶ Base R} (p q : Points d b) :
    pair d p q ≫ pullback.fst _ _ = p.val := pullback.lift_fst ..
@[simp] theorem pair_snd (d : Rˣ) {X : Scheme} {b : X ⟶ Base R} (p q : Points d b) :
    pair d p q ≫ pullback.snd _ _ = q.val := pullback.lift_snd ..

@[expose] def identityPoint (d : Rˣ) : Points d (overBase d) :=
  ⟨𝟙 _,Category.id_comp _⟩

/-- Only an actual scheme multiplication on this same carrier, with its
two unit faces, is needed for its first-order differential. In
particular no supplied scalar action or étaleness hypothesis appears. -/
structure ActualAddition (d : Rˣ) where
  map : pullback (overBase d) (overBase d) ⟶ Carrier d
  over : map ≫ overBase d = pullback.fst _ _ ≫ overBase d
  leftAxis : pair d (zeroPoint d (overBase d)) (identityPoint d) ≫ map = 𝟙 _
  rightAxis : pair d (identityPoint d) (zeroPoint d (overBase d)) ≫ map = 𝟙 _

@[expose] def sum {d : Rˣ} (A : ActualAddition d) {X : Scheme} {b : X ⟶ Base R}
    (p q : Points d b) : Points d b :=
  ⟨pair d p q ≫ A.map,by rw [Category.assoc,A.over,← Category.assoc,pair_fst,p.property]⟩

theorem sum_pull_val {d : Rˣ} (A : ActualAddition d) {X Y : Scheme} (f : X ⟶ Y)
    {b : Y ⟶ Base R} {c : X ⟶ Base R} (p q : Points d b) (p' q' : Points d c)
    (hp : f ≫ p.val = p'.val) (hq : f ≫ q.val = q'.val) :
    f ≫ (sum A p q).val = (sum A p' q').val := by
  have he : f ≫ pair d p q = pair d p' q' := by
    apply pullback.hom_ext
    · rw [Category.assoc,pair_fst,pair_fst,hp]
    · rw [Category.assoc,pair_snd,pair_snd,hq]
  change f ≫ (pair d p q ≫ A.map) = pair d p' q' ≫ A.map
  rw [← Category.assoc,he]

theorem zero_sum {d : Rˣ} (A : ActualAddition d) {X : Scheme} {b : X ⟶ Base R}
    (p : Points d b) : sum A (zeroPoint d b) p = p := by
  have H := sum_pull_val A p.val (zeroPoint d (overBase d)) (identityPoint d)
    (zeroPoint d b) p (by
      change p.val ≫ (overBase d ≫ identitySection d) = b ≫ identitySection d
      rw [← Category.assoc,p.property]) (Category.comp_id _)
  apply Subtype.ext
  exact H.symm.trans (by
    change p.val ≫ (pair d (zeroPoint d (overBase d)) (identityPoint d) ≫ A.map) = p.val
    rw [A.leftAxis,Category.comp_id])

theorem sum_zero {d : Rˣ} (A : ActualAddition d) {X : Scheme} {b : X ⟶ Base R}
    (p : Points d b) : sum A p (zeroPoint d b) = p := by
  have H := sum_pull_val A p.val (identityPoint d) (zeroPoint d (overBase d))
    p (zeroPoint d b) (Category.comp_id _) (by
      change p.val ≫ (overBase d ≫ identitySection d) = b ≫ identitySection d
      rw [← Category.assoc,p.property])
  apply Subtype.ext
  exact H.symm.trans (by
    change p.val ≫ (pair d (identityPoint d) (zeroPoint d (overBase d)) ≫ A.map) = p.val
    rw [A.rightAxis,Category.comp_id])

variable {V : Type u} [AddCommGroup V] [Module R V] [Module Rᵐᵒᵖ V] [IsCentralScalar R V]

abbrev jetBase (R V : Type u) [CommRing R] [AddCommGroup V] [Module R V]
    [Module Rᵐᵒᵖ V] [IsCentralScalar R V] :=
  Spec.algebraMap R (TrivSqZeroExt R V)

@[expose] def jetPoint (d : Rˣ) (v : V) : Points d (jetBase R V) :=
  ⟨geomJet d v,geomJet_over d v⟩

theorem jet_zero (d : Rˣ) : jetPoint d (0 : V) = zeroPoint d (jetBase R V) := by
  let S := TrivSqZeroExt R V
  have h : point d (0:V) = (Algebra.ofId R S).comp (augmentation d) := by
    have ht : augmentation d (localT d) = 0 :=
      (augmentation_map d (parameter d)).trans (origin_parameter d)
    have hz : augmentation d (localZ d) = 0 :=
      (augmentation_map d (ordinate d)).trans (origin_ordinate d)
    apply ext_local d
    · rw [point_parameter,TrivSqZeroExt.inr_zero,AlgHom.comp_apply,ht,map_zero]
    · rw [point_ordinate,AlgHom.comp_apply,hz,map_zero]
  apply Subtype.ext
  change Spec.map (CommRingCat.ofHom (point d (0:V)).toRingHom) ≫ install d =
    jetBase R V ≫ identitySection d
  rw [h]
  change Spec.map (CommRingCat.ofHom (augmentation d).toRingHom ≫
    CommRingCat.ofHom (algebraMap R S)) ≫ install d = _
  rw [Spec.map_comp,Category.assoc]
  change jetBase R V ≫ (originLift d ≫ install d) = jetBase R V ≫ identitySection d
  rw [originLift_install]

/-- The actual first-order addition on the generalized curve is +.
The V×V test followed by the fold keeps the two directions independent. -/
theorem jet_sum {d : Rˣ} (A : ActualAddition d) (a b : V) :
    jetPoint d (a+b) = sum A (jetPoint d a) (jetPoint d b) := by
  let p := jetPoint d (a,(0:V))
  let q := jetPoint d ((0:V),b)
  let P := sum A p q
  let e := zeroPoint d (𝟙 (Base R))
  have h0 : augScheme R (V×V) ≫ P.val = identitySection d := by
    have hh : e.val = identitySection d := Category.id_comp _
    have H := sum_pull_val A (augScheme R (V×V)) p q e e
      ((geomJet_reduces d _).trans hh.symm) ((geomJet_reduces d _).trans hh.symm)
    rw [sum_zero] at H
    exact H.trans hh
  obtain ⟨z,hz⟩ := exists_geomJet d P.val P.property h0
  let f₁ := LinearMap.fst R V V
  let f₂ := LinearMap.snd R V V
  have h₁ : f₁ z = a := by
    apply geomJet_injective d
    rw [← geomJet_natural d f₁ z,← hz]
    have H := sum_pull_val A (jetMap f₁) p q (jetPoint d a) (jetPoint d (0:V))
      (geomJet_natural d f₁ _) (geomJet_natural d f₁ _)
    rw [jet_zero,sum_zero] at H
    exact H
  have h₂ : f₂ z = b := by
    apply geomJet_injective d
    rw [← geomJet_natural d f₂ z,← hz]
    have H := sum_pull_val A (jetMap f₂) p q (jetPoint d (0:V)) (jetPoint d b)
      (geomJet_natural d f₂ _) (geomJet_natural d f₂ _)
    rw [jet_zero,zero_sum] at H
    exact H
  have hpair : z = (a,b) := Prod.ext h₁ h₂
  let F : V×V →ₗ[R] V := (LinearMap.id : V →ₗ[R]V).coprod LinearMap.id
  have hFa : F (a,0) = a := add_zero a
  have hFb : F (0,b) = b := zero_add b
  apply Subtype.ext
  calc
    _ = jetMap F ≫ geomJet d (a,b) := (geomJet_natural d F (a,b)).symm
    _ = jetMap F ≫ P.val := by rw [hz,hpair]
    _ = _ := sum_pull_val A (jetMap F) p q (jetPoint d a) (jetPoint d b)
      (by
        change jetMap F ≫ geomJet d (a,(0:V)) = geomJet d a
        exact (geomJet_natural d F (a,(0:V))).trans (congrArg (geomJet d) hFa))
      (by
        change jetMap F ≫ geomJet d ((0:V),b) = geomJet d b
        exact (geomJet_natural d F ((0:V),b)).trans (congrArg (geomJet d) hFb))

end SelectedGeneralizedGeometricJetAxes318

#print axioms SelectedGeneralizedGeometricJetAxes318.jet_sum
