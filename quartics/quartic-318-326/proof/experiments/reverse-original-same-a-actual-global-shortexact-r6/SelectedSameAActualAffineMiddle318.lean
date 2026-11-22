module

public import SelectedSameAActualFibreSheafArrows318
public import SelectedSameAFibreAffineProjection318
public import SelectedSameAIntrinsicPullbackSquare318
public import IntrinsicChartNormalization318
public import PullbackLineFrames318
import all SelectedSameAActualFibreSheafArrows318

/-!
# The true directional cotangent middle sheaf on a real affine chart

This identifies the actual restriction with the cotangent tensor on that chart.
Neither closed-fibre pullback nor the coefficient quotient is assumed flat.
-/

public section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct ModuleCat.Algebra

namespace SelectedSameAActualAffineMiddle318

universe u
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false

open SelectedSameAActualFibreSheafArrows318
variable {k C B : Type u} [CommRing k] [CommRing C] [CommRing B]
  [Algebra k C] [Algebra k B] [Algebra C B] [IsScalarTower k C B]
variable {X A : Scheme.{u}}

variable (σ : X ⟶ spec (D k)) (ρ : A ⟶ X) (a : A ⟶ spec k)
variable (j : spec C ⟶ X) (l : spec B ⟶ A)
variable [IsOpenImmersion j] [IsOpenImmersion l]
variable (hsq : l ≫ ρ = sMap (algebraMap C B) ≫ j)
variable (hj : j ≫ xOverK σ = sMap (algebraMap k C))
variable (hl : l ≫ a = sMap (algebraMap k B))

/-- The exact base and middle comparison at the true chart. -/
@[expose] noncomputable def middleOnChart :
    (middle σ ρ).restrict l ≅
      tilde (R := CommRingCat.of B) (ModuleCat.of B (B ⊗[C] KaehlerDifferential k C)) :=
  PullbackLineFrames318.chartIso ρ j l _ hsq (omegaX σ) ≪≫
    (Scheme.Modules.pullback (sMap (algebraMap C B))).mapIso
      (IntrinsicChartNormalization318.iso j (xOverK σ) hj).symm ≪≫
    SelectedSameAFibreAffineProjection318.tensorIso k C B

/-- The right term uses the Kähler module of the same true fibre ring. -/
@[expose] noncomputable def targetOnChart :
    (omegaA a).restrict l ≅
      tilde (R := CommRingCat.of B) (ModuleCat.of B (KaehlerDifferential k B)) :=
  (IntrinsicChartNormalization318.iso l a hl).symm

/-- The left term is compared using the canonical restriction of the
structure sheaf, not a choice of basis on the fibre. -/
@[expose] noncomputable def sourceOnChart :
    (unit A).restrict l ≅ unit (spec B) :=
  Scheme.Modules.restrictUnitIso l

/-- The actual restricted right arrow becomes exactly tilde of the literal
mapBaseChange. In particular this is not an étale cotangent isomorphism:
it is the genuine projection in the nonflat closed-fibre row. -/
theorem right_on_chart (h : ρ ≫ σ = a ≫ sMap (pr k)) :
    (Scheme.Modules.restrictFunctor l).map (right σ ρ a h) ≫
        (targetOnChart a l hl).hom =
    (middleOnChart σ ρ j l hsq hj).hom ≫ (tilde.functor (CommRingCat.of B)).map
        (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k C B)) := by
  let F := Scheme.Modules.pullback (sMap (algebraMap C B))
  let ax := (AffineIntrinsicNormalization318.algebraIso (R := k) (S := C))
  let aa := (AffineIntrinsicNormalization318.algebraIso (R := k) (S := B))
  let dx := (IntrinsicChartNormalization318.restrictionData j (xOverK σ) hj).iso
  let da := (IntrinsicChartNormalization318.restrictionData l a hl).iso
  let hp := SelectedSameAFibreAffineProjection318.over_comp k C B
  let pb := IntrinsicDifferentialPullback318.pullbackMap (sMap (algebraMap C B))
    (sMap (algebraMap k B)) (sMap (algebraMap k C)) hp
  let pa := SelectedSameAFibreAffineProjection318.right k C B
  let e := PullbackLineFrames318.chartIso ρ j l _ hsq (omegaX σ)
  have hs := SelectedSameAIntrinsicPullbackSquare318.actual_open_square_rebased
    ρ a (xOverK σ) (fibre_over_k σ ρ a h) j l (sMap (algebraMap C B)) hsq
    (sMap (algebraMap k C)) (sMap (algebraMap k B)) hj hl hp
  change (Scheme.Modules.restrictFunctor l).map (right σ ρ a h) ≫ da.hom =
    e.hom ≫ F.map dx.hom ≫ pb at hs
  have hpb : F.map ax.hom ≫ pb = pa ≫ aa.hom :=
    SelectedSameAFibreAffineProjection318.affine_intrinsic_right k C B
  have hpa : pb ≫ aa.inv = F.map ax.inv ≫ pa := by
    calc
      pb ≫ aa.inv = F.map ax.inv ≫ (F.map ax.hom ≫ pb) ≫ aa.inv := by
        simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id]
        have hId : F.map (𝟙 (FamilyIntrinsicDifferentials318.omega
            (sMap (algebraMap k C)))) = 𝟙 _ := F.map_id _
        rw [hId, Category.id_comp]
      _ = F.map ax.inv ≫ pa := by
        rw [hpb]
        simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [targetOnChart, middleOnChart, IntrinsicChartNormalization318.iso,
    Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Functor.mapIso_hom,
    Category.assoc]
  change (Scheme.Modules.restrictFunctor l).map (right σ ρ a h) ≫ da.hom ≫ aa.inv =
    e.hom ≫ F.map (dx.hom ≫ ax.inv) ≫
      (SelectedSameAFibreAffineProjection318.tensorIso k C B).hom ≫
      (tilde.functor (CommRingCat.of B)).map
        (ModuleCat.ofHom (KaehlerDifferential.mapBaseChange k C B))
  rw [← Category.assoc ((Scheme.Modules.restrictFunctor l).map _) da.hom aa.inv, hs]
  simp only [Category.assoc, hpa, Functor.map_comp]
  rw [← SelectedSameAFibreAffineProjection318.right_on_tensor k C B] <;> rfl

end SelectedSameAActualAffineMiddle318
