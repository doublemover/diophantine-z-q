module
public import RelativeOriginalClassRestriction318
public section
noncomputable section
namespace RelativeAmbientReassociation318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {C S R B T : Scheme.{u}} (p : C ⟶ S) (r : R ⟶ S) (b : B ⟶ R)
local notation "q" => pullback.snd p r
abbrev original : pullback q b ⟶ C := pullback.fst q b ≫ pullback.fst p r
lemma cartesian : IsPullback (original p r b) (pullback.snd q b) p (b ≫ r) :=
  ((IsPullback.of_hasPullback q b).flip.paste_vert (IsPullback.of_hasPullback p r).flip).flip
/-- Literal reassociation of the SAME original curve, preserving both
original-source and parameter projections over arbitrary schemes. -/
@[expose] def comparison : pullback q b ≅ pullback p (b ≫ r) := (cartesian p r b).isoPullback
@[reassoc] lemma first : (comparison p r b).hom ≫ pullback.fst p (b ≫ r)=original p r b :=
  (cartesian p r b).isoPullback_hom_fst
@[reassoc] lemma second : (comparison p r b).hom ≫ pullback.snd p (b ≫ r)=pullback.snd q b :=
  (cartesian p r b).isoPullback_hom_snd
/-- Actual scheme equality of the coefficient square between the two
reassociated families, not a comparison of only their points. -/
lemma natural (t : T ⟶ R) (j : T ⟶ B) (hj : j ≫ b=t) :
    RelativeSchemeCoefficient318.map q b t j hj ≫ (comparison p r b).hom=
      (comparison p r t).hom ≫ RelativeSchemeCoefficient318.map p (b ≫ r) (t ≫ r) j
        (by rw [←Category.assoc,hj]) := by
  apply pullback.hom_ext
  · simp only [Category.assoc,first,RelativeSchemeCoefficient318.map_fst,original]
    rw [←Category.assoc,RelativeSchemeCoefficient318.map_fst]
  · simp only [Category.assoc,second,RelativeSchemeCoefficient318.map_snd]
end RelativeAmbientReassociation318
