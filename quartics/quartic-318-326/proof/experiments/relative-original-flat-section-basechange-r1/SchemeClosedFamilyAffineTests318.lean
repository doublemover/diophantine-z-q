module
public import ContactQuotientUniversalTest318
public import SchemeMonoLocalLift318
public section
noncomputable section
namespace SchemeClosedFamilyAffineTests318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y Z B : Scheme.{u}} (p : X ⟶ B) (q : Y ⟶ X) (r : Z ⟶ X)
  [IsClosedImmersion q] [IsClosedImmersion r]
local notation "U" => B.affineOpenCover.openCover
/-- Local source-preserving isomorphisms on ALL affine base charts
produce a genuine global morphism between the unchanged closed families. -/
@[expose] def lift
    (e : ∀ i, pullback (q ≫ p) (U.f i) ≅ pullback (r ≫ p) (U.f i))
    (he : ∀ i, (e i).hom ≫ pullback.fst (r ≫ p) (U.f i) ≫ r=
      pullback.fst (q ≫ p) (U.f i) ≫ q) : Y ⟶ Z :=
  SchemeMonoLocalLift318.lift (U.pullback₁ (q ≫ p)) r q
    (fun i => (e i).hom ≫ pullback.fst (r ≫ p) (U.f i)) (by
      intro i
      simpa only [Category.assoc] using he i)
@[reassoc] lemma lift_into
    (e : ∀ i, pullback (q ≫ p) (U.f i) ≅ pullback (r ≫ p) (U.f i))
    (he : ∀ i, (e i).hom ≫ pullback.fst (r ≫ p) (U.f i) ≫ r=
      pullback.fst (q ≫ p) (U.f i) ≫ q) : lift p q r e he ≫ r=q :=
  SchemeMonoLocalLift318.lift_factor _ _ _ _ _
/-- Because both maps are actual closed embeddings, inverse and cocycle
coherence follow from monomorphism cancellation, not additional choices. -/
@[expose] def iso
    (e : ∀ i, pullback (q ≫ p) (U.f i) ≅ pullback (r ≫ p) (U.f i))
    (he : ∀ i, (e i).hom ≫ pullback.fst (r ≫ p) (U.f i) ≫ r=
      pullback.fst (q ≫ p) (U.f i) ≫ q) : Y ≅ Z where
  hom := lift p q r e he
  inv := lift p r q (fun i => (e i).symm) (by
    intro i
    rw [← he i]
    simp only [Iso.symm_hom,← Category.assoc,Iso.inv_hom_id,Category.id_comp])
  hom_inv_id := by
    apply (cancel_mono q).mp
    simp only [Category.assoc,lift_into,Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono r).mp
    simp only [Category.assoc,lift_into,Category.id_comp]
@[reassoc] lemma iso_into
    (e : ∀ i, pullback (q ≫ p) (U.f i) ≅ pullback (r ≫ p) (U.f i))
    (he : ∀ i, (e i).hom ≫ pullback.fst (r ≫ p) (U.f i) ≫ r=
      pullback.fst (q ≫ p) (U.f i) ≫ q) : (iso p q r e he).hom ≫ r=q := lift_into p q r e he
end SchemeClosedFamilyAffineTests318
