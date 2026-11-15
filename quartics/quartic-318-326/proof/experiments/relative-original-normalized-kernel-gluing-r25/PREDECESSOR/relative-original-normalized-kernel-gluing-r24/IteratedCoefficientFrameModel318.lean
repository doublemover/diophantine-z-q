module
public import ContactCanonicalTrivializationParameter318
public section
noncomputable section
namespace IteratedCoefficientFrameModel318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {X B S T : Scheme.{u}} (p : X ⟶ B) (b : S ⟶ B) (a : T ⟶ S)
abbrev original := pullback.fst p b
abbrev projection := pullback.snd p b
abbrev inner := pullback.fst (projection p b) a
abbrev composite := inner p b a ≫ original p b
abbrev coefficient := RelativeSchemeCoefficient318.map p b (a ≫ b) a rfl
/-- Actual direct and iterated coefficient families, retaining the original
source projection AND coefficient projection on the entire schemes. -/
@[expose] def model : pullback p (a ≫ b) ≅ pullback (projection p b) a :=
  (RelativeSchemeCoefficient318.cartesian p b (a ≫ b) a rfl).isoPullback
@[reassoc] lemma model_inner : (model p b a).hom ≫ inner p b a=coefficient p b a :=
  (RelativeSchemeCoefficient318.cartesian p b (a ≫ b) a rfl).isoPullback_hom_fst
@[reassoc] lemma model_base : (model p b a).hom ≫ pullback.snd (projection p b) a=
    pullback.snd p (a ≫ b) :=
  (RelativeSchemeCoefficient318.cartesian p b (a ≫ b) a rfl).isoPullback_hom_snd
@[reassoc] lemma model_source : (model p b a).hom ≫ composite p b a=pullback.fst p (a ≫ b) := by
  rw [composite,←Category.assoc,model_inner]
  exact RelativeSchemeCoefficient318.map_fst p b (a ≫ b) a rfl
variable {T' : Scheme.{u}} (a' : T' ⟶ S) (h : T' ⟶ T) (hh : h ≫ a=a')
abbrev directChange := RelativeSchemeCoefficient318.map p (a ≫ b) (a' ≫ b) h
  (by rw [←Category.assoc,hh])
abbrev nestedChange := RelativeSchemeCoefficient318.map (projection p b) a a' h hh
/-- The actual family-model isomorphisms commute with EVERY coefficient
arrow. Both equalities are proved on full scheme pullback projections. -/
lemma model_square : (model p b a').hom ≫ nestedChange p b a a' h hh=
    directChange p b a a' h hh ≫ (model p b a).hom := by
  apply pullback.hom_ext
  · rw [Category.assoc,RelativeSchemeCoefficient318.map_fst,model_inner,
      Category.assoc,model_inner]
    apply pullback.hom_ext
    · simp only [Category.assoc,RelativeSchemeCoefficient318.map_fst]
    · simp only [Category.assoc,RelativeSchemeCoefficient318.map_snd,hh]
  · rw [Category.assoc,RelativeSchemeCoefficient318.map_snd,←Category.assoc,model_base,
      Category.assoc,model_base,RelativeSchemeCoefficient318.map_snd]
end IteratedCoefficientFrameModel318
