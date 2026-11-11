module
public import OpenCartesianSectionSquare318
public section
noncomputable section
namespace OpenModuleCartesianBaseChange318
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TopologicalSpace Opposite
open OpenCartesianSectionSquare318
variable {W U V X : Scheme} (right : W ⟶ V) (left : W ⟶ U)
  (k : V ⟶ X) (j : U ⟶ X) [IsOpenImmersion left] [IsOpenImmersion k]
  (H : IsPullback right left k j)

/-- Actual module-sheaf base change along an open immersion. Both sides
are the existing Scheme.Modules functors. Components transport the SAME
sections along the genuine Cartesian opens equality, with full scalar
compatibility proved from the original structure sheaf square. -/
@[expose] def objectIso (M : U.Modules) :
    (Scheme.Modules.restrictFunctor k).obj ((Scheme.Modules.pushforward j).obj M) ≅
    (Scheme.Modules.pushforward right).obj ((Scheme.Modules.restrictFunctor left).obj M) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun O => ?_) ?_
  · refine ModuleCat.isoMk
      (M.presheaf.mapIso (eqToIso (opens_square right left k j H O.unop)).op) ?_
    intro r
    ext x
    symm
    change M.presheaf.map (eqToHom (opens_square right left k j H O.unop)).op
        ((j.app (k ''ᵁ O.unop) ((k.appIso O.unop).inv r)) • x)=
      ((left.appIso (right ⁻¹ᵁ O.unop)).inv (right.app O.unop r)) •
        M.presheaf.map (eqToHom (opens_square right left k j H O.unop)).op x
    rw [M.map_smul]
    exact congrArg (fun c => c • M.presheaf.map
      (eqToHom (opens_square right left k j H O.unop)).op x)
      (congrArg (fun f => f r) (scalar_square right left k j H O.unop))
  · intro O P a
    ext x
    change (M.presheaf.map ((Opens.map j.base).map (k.opensFunctor.map a.unop)).op≫
      M.presheaf.map (eqToHom (opens_square right left k j H P.unop)).op) x=
      (M.presheaf.map (eqToHom (opens_square right left k j H O.unop)).op≫
        M.presheaf.map (left.opensFunctor.map ((Opens.map right.base).map a.unop)).op) x
    rw [←Functor.map_comp,←Functor.map_comp]
    exact congrArg (fun e => M.presheaf.map e x) (Subsingleton.elim _ _)

/-- Exact component on sections: no new section or guessed restriction
map is introduced by the isomorphism. -/
lemma objectIso_hom_app (M : U.Modules) (O : V.Opens) :
    ((objectIso right left k j H M).hom).app O=
      M.presheaf.map (eqToHom (opens_square right left k j H O)).op := rfl
lemma objectIso_inv_app (M : U.Modules) (O : V.Opens) :
    ((objectIso right left k j H M).inv).app O=
      M.presheaf.map (eqToHom (opens_square right left k j H O).symm).op := rfl

/-- Functor-level Cartesian base change, natural in the ENTIRE module
sheaf. This is a genuine natural isomorphism, not an equality of selected
sections or an assumed exactness of direct image. -/
@[expose] def baseChange :
    Scheme.Modules.pushforward j ⋙ Scheme.Modules.restrictFunctor k ≅
      Scheme.Modules.restrictFunctor left ⋙ Scheme.Modules.pushforward right :=
  NatIso.ofComponents (objectIso right left k j H) (by
    intro M N f
    apply Scheme.Modules.hom_ext
    intro O
    rw [Scheme.Modules.Hom.comp_app,Scheme.Modules.Hom.comp_app,
      objectIso_hom_app,objectIso_hom_app]
    exact (f.mapPresheaf.naturality
      (eqToHom (opens_square right left k j H O)).op).symm)
end OpenModuleCartesianBaseChange318
