module
public import SchemeClosedFamilyAffineTests318
public section
noncomputable section
namespace SchemeClosedFamilyLocalModels318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X Y Z B : Scheme.{u}} (p : X ⟶ B) (q : Y ⟶ X) (r : Z ⟶ X)
  [IsClosedImmersion q] [IsClosedImmersion r]
local notation "U" => B.affineOpenCover.openCover
/-- Genuine local shared models over the WHOLE affine base cover. -/
structure Data where
  family : U.I₀ → Scheme.{u}
  projection : ∀ i, family i ⟶ U.X i
  left : ∀ i, family i ⟶ Y
  right : ∀ i, family i ⟶ Z
  left_cartesian : ∀ i, IsPullback (left i) (projection i) (q ≫ p) (U.f i)
  right_cartesian : ∀ i, IsPullback (right i) (projection i) (r ≫ p) (U.f i)
  over_source : ∀ i, left i ≫ q=right i ≫ r
variable (D : Data p q r)
@[expose] def localIso (i : U.I₀) : pullback (q ≫ p) (U.f i) ≅ pullback (r ≫ p) (U.f i) :=
  (D.left_cartesian i).isoPullback.symm ≪≫ (D.right_cartesian i).isoPullback
lemma localIso_source (i : U.I₀) : (localIso p q r D i).hom ≫ pullback.fst (r ≫ p) (U.f i) ≫ r=
    pullback.fst (q ≫ p) (U.f i) ≫ q := by
  simp only [localIso,Iso.trans_hom,Iso.symm_hom,Category.assoc,
    (D.right_cartesian i).isoPullback_hom_fst]
  rw [← D.over_source i,← Category.assoc,(D.left_cartesian i).isoPullback_inv_fst]
/-- Actual source-preserving global isomorphism from shared local models. -/
@[expose] def iso : Y ≅ Z := SchemeClosedFamilyAffineTests318.iso p q r
  (localIso p q r D) (localIso_source p q r D)
@[reassoc] lemma iso_into : (iso p q r D).hom ≫ r=q :=
  SchemeClosedFamilyAffineTests318.iso_into p q r _ _
end SchemeClosedFamilyLocalModels318
