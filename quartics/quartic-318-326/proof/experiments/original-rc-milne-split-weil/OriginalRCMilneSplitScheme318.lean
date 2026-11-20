module
public import OriginalRCMilneSplitQuadratic318
public import Mathlib.AlgebraicGeometry.Limits

public section
noncomputable section

namespace OriginalRCMilneSplitScheme318

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open OriginalRCMilneSplitQuadratic318
open scoped TensorProduct

universe u
variable {R F : Type u} [CommRing R] [Field F] [CharZero F] [Algebra R F]

abbrev splitTrait (k : R) := F ⊗[R] QuadraticAlgebra R k 0

variable (k : R) (s : F) (hs : s^2 = algebraMap R F k) (hs0 : s ≠ 0)

/-- The literal pullback of Spec K to Spec F is the two ordered
copies of Spec F; the first copy uses the chosen square root. -/
@[expose] def chart :
    Spec (CommRingCat.of (splitTrait (F:=F) k)) ≅
      Spec (CommRingCat.of F) ⨿ Spec (CommRingCat.of F) :=
  Scheme.Spec.mapIso (splitBase k s hs hs0).toRingEquiv.toCommRingCatIso.symm.op ≪≫
    (asIso (coprodSpec F F)).symm

theorem chart_inl :
    coprod.inl ≫ (chart k s hs hs0).inv =
      Spec.map (CommRingCat.ofHom
        ((RingHom.fst F F).comp (splitBase k s hs hs0).toAlgHom.toRingHom)) := by
  simp only [chart,Iso.trans_inv,Iso.symm_inv,asIso_hom,←Category.assoc,coprodSpec_inl,
    ←Spec.map_comp] <;> rfl

theorem chart_inr :
    coprod.inr ≫ (chart k s hs hs0).inv =
      Spec.map (CommRingCat.ofHom
        ((RingHom.snd F F).comp (splitBase k s hs hs0).toAlgHom.toRingHom)) := by
  simp only [chart,Iso.trans_inv,Iso.symm_inv,asIso_hom,←Category.assoc,coprodSpec_inr,
    ←Spec.map_comp] <;> rfl

/-- The actual pullback of the global chosen field's Spec, rather
than only an isomorphism of its abstract generic ring. -/
@[expose] def pullbackChart :
    pullback (Spec.map (CommRingCat.ofHom (algebraMap R F)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (QuadraticAlgebra R k 0)))) ≅
      Spec (CommRingCat.of F) ⨿ Spec (CommRingCat.of F) :=
  pullbackSpecIso R F (QuadraticAlgebra R k 0) ≪≫ chart k s hs hs0

theorem chart_inl_base :
    (coprod.inl ≫ (chart k s hs hs0).inv) ≫
        Spec.algebraMap F (splitTrait (F:=F) k) = 𝟙 _ := by
  rw [chart_inl, ←Spec.map_comp]
  have he : ((RingHom.fst F F).comp (splitBase k s hs hs0).toAlgHom.toRingHom).comp
      (algebraMap F (splitTrait (F:=F) k)) = RingHom.id F := by
    apply RingHom.ext
    intro a
    exact congrArg Prod.fst ((splitBase k s hs hs0).commutes a)
  change Spec.map (CommRingCat.ofHom _) = _
  rw [he] <;> simp only [Spec.map_id]

theorem chart_inr_base :
    (coprod.inr ≫ (chart k s hs hs0).inv) ≫
        Spec.algebraMap F (splitTrait (F:=F) k) = 𝟙 _ := by
  rw [chart_inr, ←Spec.map_comp]
  have he : ((RingHom.snd F F).comp (splitBase k s hs hs0).toAlgHom.toRingHom).comp
      (algebraMap F (splitTrait (F:=F) k)) = RingHom.id F := by
    apply RingHom.ext
    intro a
    exact congrArg Prod.snd ((splitBase k s hs hs0).commutes a)
  change Spec.map (CommRingCat.ofHom _) = _
  rw [he] <;> simp only [Spec.map_id]

/-- Yoneda point comparison on the literal split base. No elliptic
scheme/Weil restriction is postulated by this ordinary Hom equivalence. -/
def homPair (X : Scheme.{u}) :
    (Spec (CommRingCat.of (splitTrait (F:=F) k)) ⟶ X) ≃
      ((Spec (CommRingCat.of F) ⟶ X) × (Spec (CommRingCat.of F) ⟶ X)) where
  toFun f := (coprod.inl ≫ (chart k s hs hs0).inv ≫ f,
    coprod.inr ≫ (chart k s hs hs0).inv ≫ f)
  invFun z := (chart k s hs hs0).hom ≫ coprod.desc z.1 z.2
  left_inv f := by
    have h : coprod.desc (coprod.inl ≫ (chart k s hs hs0).inv ≫ f)
        (coprod.inr ≫ (chart k s hs hs0).inv ≫ f) = (chart k s hs hs0).inv ≫ f := by
      apply coprod.hom_ext <;> simp only [coprod.inl_desc,coprod.inr_desc]
    change (chart k s hs hs0).hom ≫ _ = f
    rw [h,←Category.assoc,Iso.hom_inv_id,Category.id_comp]
  right_inv z := by
    apply Prod.ext <;>
      simp only [Iso.inv_hom_id_assoc,coprod.inl_desc,coprod.inr_desc]

end OriginalRCMilneSplitScheme318

#print axioms OriginalRCMilneSplitScheme318.homPair
