module
public import PELOriginalCharacterAllOpenDescent318
public section
noncomputable section
namespace PELOriginalCharacterInvariantPresheaf318
open AlgebraicGeometry CategoryTheory Opposite
open PELOriginalWholeCharacterMorphisms318 PELOriginalCharacterInvariantSections318

/-- The literal invariant-section rings with ACTUAL restriction maps.
Neither objects nor restrictions are replaced by transported surrogates. -/
@[expose] def invariantPresheaf (i:Fin 4):((Curve i).Opens)ᵒᵖ⥤CommRingCat where
  obj U:=CommRingCat.of (invariantSubring i U.unop)
  map j:=CommRingCat.ofHom (restrict i j.unop)
  map_id U:=by
    apply CommRingCat.hom_ext
    ext x
    obtain ⟨a,rfl⟩:=(sectionEquiv i U.unop).surjective x
    change restrict i (𝟙 U.unop) (sectionEquiv i U.unop a)=sectionEquiv i U.unop a
    rw [restriction_square]
    simp
  map_comp {U V W} f g:=by
    apply CommRingCat.hom_ext
    ext x
    obtain ⟨a,rfl⟩:=(sectionEquiv i U.unop).surjective x
    change restrict i (f≫g).unop (sectionEquiv i U.unop a)=
      restrict i g.unop (restrict i f.unop (sectionEquiv i U.unop a))
    simp only [restriction_square]
    exact congrArg (sectionEquiv i W.unop)
      (congrArg (fun k:Γ(Curve i,U.unop)⟶Γ(Curve i,W.unop)=>k a)
        ((Curve i).presheaf.map_comp f g))

/-- A bundled natural isomorphism on ALL target opens between the actual
structure presheaf and the literal invariant regular sections of the
full source inverse images. Empty opens are included. This is not a
categorical quotient theorem for arbitrary scheme-valued maps. -/
@[expose] def structureIso (i:Fin 4):(Curve i).presheaf≅invariantPresheaf i:=
  NatIso.ofComponents (fun U=>(sectionEquiv i U.unop).toCommRingCatIso) (by
    intro U V f
    apply CommRingCat.hom_ext
    ext a
    exact (restriction_square i f.unop a).symm)

/-- Each component remains the SAME original whole character section
pullback after the literal invariant-ring inclusion. -/
lemma structureIso_component (i:Fin 4) (U:(Curve i).Opens) (a:Γ(Curve i,U)):
    (((structureIso i).hom.app (op U) a):
      Γ(PELOriginalCharacterPullback318.Model,morphism i⁻¹ᵁU))=(morphism i).app U a:=rfl
end PELOriginalCharacterInvariantPresheaf318
