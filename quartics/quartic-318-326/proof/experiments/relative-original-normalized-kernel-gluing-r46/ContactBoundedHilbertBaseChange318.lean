module
public import ContactBoundedSchemeHilbertData318
public section
noncomputable section
namespace ContactBoundedHilbertBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
variable (c : Fin 4 → ℚˣ) (N : ℕ) {B T : Scheme.{0}}
  (b : B ⟶ Spec (CommRingCat.of ℚ)) (t : T ⟶ Spec (CommRingCat.of ℚ))
  (g : T ⟶ B) (hg : g ≫ b=t) (D : ContactBoundedSchemeHilbertData318.Data c N b)
local notation "p" => ContactIntrinsicDifferentials318.structureMap c
abbrev sourceMap := RelativeSchemeCoefficient318.map p b t g hg
abbrev ideal := D.ideal.comap (sourceMap c b t g hg)
abbrev toFamily := IdealSheafCoefficientCartesian318.map D.ideal (sourceMap c b t g hg)
abbrev projection := (ideal c N b t g hg D).subschemeι ≫ pullback.snd p t
lemma cartesian : IsPullback (toFamily c N b t g hg D) (projection c N b t g hg D)
    (ContactBoundedSchemeHilbertData318.projection c N b D) g :=
  (IdealSheafCoefficientCartesian318.cartesian D.ideal (sourceMap c b t g hg)).paste_vert
    (RelativeSchemeCoefficient318.cartesian p b t g hg)
/-- The genuine full ideal coefficient action preserves a bound without
assuming rank is constant on the whole coefficient scheme. -/
@[expose] def map : ContactBoundedSchemeHilbertData318.Data c N t where
  ideal := ideal c N b t g hg D
  finite := MorphismProperty.of_isPullback (cartesian c N b t g hg D) inferInstance
  flat := MorphismProperty.of_isPullback (cartesian c N b t g hg D) inferInstance
  presentation := MorphismProperty.of_isPullback (cartesian c N b t g hg D) inferInstance
  bound z := by
    rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ (cartesian c N b t g hg D)]
    exact D.bound _
lemma rank (z : T) : (ContactBoundedSchemeHilbertData318.projection c N t (map c N b t g hg D)).finrank z=
    (ContactBoundedSchemeHilbertData318.projection c N b D).finrank (g z) :=
  Scheme.Hom.finrank_of_isPullback _ _ _ _ (cartesian c N b t g hg D) z
end ContactBoundedHilbertBaseChange318
