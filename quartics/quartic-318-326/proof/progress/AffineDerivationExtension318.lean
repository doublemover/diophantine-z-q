module
public import AffineBasicDerivation318
public section
noncomputable section
namespace AffineDerivationExtension318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
universe u

variable {S : CommRingCat.{u}} (M : (Spec S).Modules)
    (δ : S →+ Γ(M,⊤))
    (hδ : ∀ a b : S, δ (a*b)=a • δ b + b • δ a)

/-- Actual compatible localized derivatives on the affine basic-open basis. -/
@[expose] def basicMap :
    (inducedFunctor (PrimeSpectrum.basicOpen (R:=S))).op ⋙
      ((Spec S).presheaf ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) ⟶
    (inducedFunctor (PrimeSpectrum.basicOpen (R:=S))).op ⋙ M.presheaf where
  app s := AddCommGrpCat.ofHom
    (AffineBasicDerivation318.basicDerivation M δ hδ s.unop).toLinearMap.toAddMonoidHom
  naturality {s t} i := by
    ext a
    exact AffineBasicDerivation318.basic_naturality M δ hδ s.unop t.unop
      (leOfHom ((inducedFunctor (PrimeSpectrum.basicOpen (R:=S))).map i.unop)) a

/-- Extend the compatible additive maps from the actual affine basis by the
sheaf's genuine basis-extension equivalence. -/
@[expose] def additiveMap :
    (Spec S).presheaf ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat) ⟶
      M.presheaf :=
  TopCat.Sheaf.restrictHomEquivHom _ ⟨M.presheaf,M.isSheaf⟩
    PrimeSpectrum.isBasis_basic_opens (basicMap M δ hδ)

theorem additiveMap_basic (s : S) :
    (additiveMap M δ hδ).app (op (PrimeSpectrum.basicOpen s)) =
      (basicMap M δ hδ).app (op s) := by
  have hh := (TopCat.Sheaf.restrictHomEquivHom
    ((Spec S).presheaf ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
    ⟨M.presheaf,M.isSheaf⟩ (B:=PrimeSpectrum.basicOpen (R:=S))
    PrimeSpectrum.isBasis_basic_opens).left_inv (basicMap M δ hδ)
  exact congrArg (fun k => k.app (op s)) hh

theorem additiveMap_basic_algebraMap (s a : S) :
    (additiveMap M δ hδ).app (op (PrimeSpectrum.basicOpen s))
      (algebraMap S Γ(Spec S,PrimeSpectrum.basicOpen s) a) =
        AffineBasicDerivation318.restrictTop M s (δ a) := by
  rw [additiveMap_basic]
  exact AffineBasicDerivation318.basic_algebraMap M δ hδ s a

theorem additiveMap_top (a : S) :
    (additiveMap M δ hδ).app (op ⊤) ((Scheme.ΓSpecIso S).inv a) = δ a := by
  have h := additiveMap_basic_algebraMap M δ hδ (1:S) a
  change (additiveMap M δ hδ).app (op (PrimeSpectrum.basicOpen (1:S)))
    ((Spec S).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso S).inv a)) =
      M.presheaf.map (homOfLE le_top).op (δ a) at h
  rw [show PrimeSpectrum.basicOpen (1:S) = ⊤ from PrimeSpectrum.basicOpen_one] at h
  change (additiveMap M δ hδ).app (op ⊤)
    ((Spec S).presheaf.map (𝟙 (op ⊤)) ((Scheme.ΓSpecIso S).inv a)) =
      M.presheaf.map (𝟙 (op ⊤)) (δ a) at h
  have hr := congrArg (fun k => k ((Scheme.ΓSpecIso S).inv a))
    ((Spec S).presheaf.map_id (op ⊤))
  have hm := congrArg (fun k => k (δ a)) (M.presheaf.map_id (op ⊤))
  exact (congrArg ((additiveMap M δ hδ).app (op ⊤)) hr).symm.trans (h.trans hm)

variable {R : CommRingCat.{u}} (f : R ⟶ S)

/-- Every global relative derivation extends to a genuine sheaf derivation on
all opens of the actual affine scheme. -/
@[expose] def extend (d : (moduleSpecΓFunctor.obj M).Derivation f) :
    PresheafOfModulesOfCommRing.Derivation' M.val (AffineIntrinsicComparison318.coefficients f) := by
  let δ : S →+ Γ(M,⊤) := AddMonoidHom.mk' d.d (by intro a b; exact d.d_add a b)
  have hδ : ∀ a b : S, δ (a*b)=a • δ b + b • δ a := d.d_mul
  refine DerivationFromBasis318.fromBasis (additiveMap M δ hδ) ?_ ?_
  · intro s a b
    rw [additiveMap_basic]
    exact (AffineBasicDerivation318.basicDerivation M δ hδ s).leibniz a b
  · intro s a
    change (additiveMap M δ hδ).app (op (PrimeSpectrum.basicOpen s))
      (algebraMap S Γ(Spec S,PrimeSpectrum.basicOpen s) (f a)) = 0
    rw [additiveMap_basic_algebraMap]
    change AffineBasicDerivation318.restrictTop M s (d.d (f a)) = 0
    rw [d.d_map,map_zero]

theorem extend_top (d : (moduleSpecΓFunctor.obj M).Derivation f) (s : S) :
    (extend M f d).d ((Scheme.ΓSpecIso S).inv s) = d.d s :=
  additiveMap_top M (AddMonoidHom.mk' d.d (by intro a b; exact d.d_add a b)) d.d_mul s

/-- Global evaluation and sheaf extension are inverse: existence and uniqueness
are both theorems about the actual affine scheme. -/
theorem extend_topDerivation
    (d : PresheafOfModulesOfCommRing.Derivation' M.val (AffineIntrinsicComparison318.coefficients f)) :
    extend M f (AffineIntrinsicComparison318.topDerivation f d)=d := by
  apply AffineDerivationDetermination318.ext_top
  intro z
  have hz := Iso.hom_inv_id_apply (Scheme.ΓSpecIso S) z
  rw [←hz,extend_top]
  rfl

theorem topDerivation_extend (d : (moduleSpecΓFunctor.obj M).Derivation f) :
    AffineIntrinsicComparison318.topDerivation f (extend M f d)=d := by
  letI := f.hom.toAlgebra
  letI := Module.compHom (moduleSpecΓFunctor.obj M) f.hom
  apply _root_.Derivation.ext
  intro s
  exact extend_top M f d s
end AffineDerivationExtension318
