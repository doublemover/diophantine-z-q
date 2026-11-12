module
public import ContactSchemeHilbertEquiv318
public section
noncomputable section
namespace ContactSchemeHilbertBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (n : ℕ) {B T : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (t : T ⟶ Spec (CommRingCat.of ℚ))
  (g : T ⟶ B) (hg : g ≫ b=t) (D : ContactSchemeHilbertData318.Data c n b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
abbrev sourceMap := RelativeSchemeCoefficient318.map p b t g hg
abbrev ideal := D.ideal.comap (sourceMap c b t g hg)
abbrev toFamily := IdealSheafCoefficientCartesian318.map D.ideal (sourceMap c b t g hg)
abbrev projection := (ideal c n b t g hg D).subschemeι ≫ pullback.snd p t
lemma cartesian : IsPullback (toFamily c n b t g hg D) (projection c n b t g hg D)
    (ContactSchemeHilbertData318.projection c n b D) g :=
  (IdealSheafCoefficientCartesian318.cartesian D.ideal (sourceMap c b t g hg)).paste_vert
    (RelativeSchemeCoefficient318.cartesian p b t g hg)
/-- Coefficient action on arbitrary schemes is literal full ideal
comap, with standard properties and every fiber rank DERIVED. -/
@[expose] def map : ContactSchemeHilbertData318.Data c n t where
  ideal := ideal c n b t g hg D
  finite := MorphismProperty.of_isPullback (cartesian c n b t g hg D) inferInstance
  flat := MorphismProperty.of_isPullback (cartesian c n b t g hg D) inferInstance
  presentation := MorphismProperty.of_isPullback (cartesian c n b t g hg D) inferInstance
  rank z := by
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (cartesian c n b t g hg D)]
    exact D.rank _
@[expose] def pointMap (f : ContactSchemePointFamily318.SchemePoint c n b) : ContactSchemePointFamily318.SchemePoint c n t :=
  ⟨g ≫ f.val,by rw [Category.assoc,f.property]; exact hg⟩
end ContactSchemeHilbertBaseChange318
