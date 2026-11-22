module

public import OpenPullbackStructure318

/-!
# The actual module pushforward on a genuine open pullback

The sections on both sides are sections of the same actual module,
on the same actual inverse-image open. Use the proved equality of
opens and the same structural scalar square; do not replace the
module by a newly chosen affine presentation.
-/

public section
noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

namespace SelectedSameAActualPushforwardRestriction318

universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {P X U Y : Scheme.{u}} (q : P ⟶ U) (k : P ⟶ X) (j : U ⟶ Y)
  (f : X ⟶ Y) [IsOpenImmersion k] [IsOpenImmersion j]
  (H : IsPullback q k j f) (M : X.Modules)

abbrev leftObj := ((Scheme.Modules.pushforward f).obj M).restrict j
abbrev rightObj := (Scheme.Modules.pushforward q).obj (M.restrict k)

abbrev leftOpen (W : U.Opens) := f ⁻¹ᵁ (j ''ᵁ W)
abbrev rightOpen (W : U.Opens) := k ''ᵁ (q ⁻¹ᵁ W)

@[expose] def openEq (W : U.Opens) : rightOpen q k W = leftOpen j f W :=
  OpenPullbackStructure318.opens_eq q k j f H W

/-- Exact underlying additive comparison on the whole original open. -/
@[expose] def comparedSections (W : U.Opens) :
    Γ(M,leftOpen j f W) ≅ Γ(M,rightOpen q k W) :=
  M.presheaf.mapIso (eqToIso (openEq q k j f H W)).op

/-- The scalar action on the comparison uses the same square as the
actual structure-sheaf comparison. -/
theorem scalar_comparison (W : U.Opens) (a : Γ(U,W)) :
    X.presheaf.map (eqToHom (openEq q k j f H W)).op
        (f.app (j ''ᵁ W) ((j.appIso W).inv a)) =
      (k.appIso (q ⁻¹ᵁ W)).inv (q.app W a) := by
  apply (ConcreteCategory.bijective_of_isIso (k.appIso (q ⁻¹ᵁ W)).hom).1
  have h := congrArg (fun m => m ((j.appIso W).inv a))
    (OpenPullbackStructure318.scalar_square q k j f H W)
  change (k.appIso (q ⁻¹ᵁ W)).hom
      (X.presheaf.map (eqToHom (openEq q k j f H W)).op
        (f.app (j ''ᵁ W) ((j.appIso W).inv a))) =
    q.app W ((j.appIso W).hom ((j.appIso W).inv a)) at h
  simpa only [Iso.inv_hom_id_apply] using h

/-- Actual restriction of the pushed-forward module, with the same
module on the Cartesian open chart. This is a restriction
comparison, not a claim about general base change for pushforward. -/
@[expose] def iso :
    leftObj j f M ≅ rightObj q k M := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso <|
    PresheafOfModules.isoMk (fun W => ?_) ?_
  · refine ModuleCat.isoMk (comparedSections q k j f H M W.unop) ?_
    intro b
    ext s
    let e := eqToHom (openEq q k j f H W.unop)
    change (k.appIso (q ⁻¹ᵁ W.unop)).inv (q.app W.unop b) •
        M.presheaf.map e.op s =
      M.presheaf.map e.op
        (f.app (j ''ᵁ W.unop) ((j.appIso W.unop).inv b) • s)
    rw [Scheme.Modules.map_smul, scalar_comparison q k j f H W.unop b]
  · intro W Z g
    ext s
    let v := leOfHom g.unop
    let l := homOfLE (f.preimage_mono (j.image_mono v))
    let r := homOfLE (k.image_mono (q.preimage_mono v))
    let eW := eqToHom (openEq q k j f H W.unop)
    let eZ := eqToHom (openEq q k j f H Z.unop)
    change
      M.presheaf.map eZ.op (M.presheaf.map l.op s) =
        M.presheaf.map r.op (M.presheaf.map eW.op s)
    have hcomp : l.op ≫ eZ.op = eW.op ≫ r.op := Subsingleton.elim _ _
    rw [← M.presheaf.map_comp_apply, ← M.presheaf.map_comp_apply, hcomp]

end SelectedSameAActualPushforwardRestriction318
