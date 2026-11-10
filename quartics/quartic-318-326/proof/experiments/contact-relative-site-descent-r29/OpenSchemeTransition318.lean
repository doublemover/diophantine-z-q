module
public import OpenSheafRestrictionCompatibility318
public section
noncomputable section
namespace OpenSchemeTransition318
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open OpenSheafTransition318 OpenSheafRestrictionCompatibility318 OpenChartModuleImages318
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {X : Scheme.{u}} {A B C : X.Modules} {V : X.Opens}

lemma toOver_trans (e : A.restrict V.ι ≅ B.restrict V.ι)
    (f : B.restrict V.ι ≅ C.restrict V.ι) :
    toOverIso V (e ≪≫ f) = toOverIso V e ≪≫ toOverIso V f := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv V).functor.map_injective
  simp only [Iso.trans_hom, Functor.map_comp, map_toOver_hom, Category.assoc,
    Iso.inv_hom_id_assoc]

lemma toOver_refl : toOverIso V (Iso.refl (A.restrict V.ι)) = Iso.refl (A.over V) := by
  apply Iso.ext
  apply (Scheme.Modules.overEquiv V).functor.map_injective
  simp only [map_toOver_hom, Iso.refl_hom, Functor.map_id, Category.id_comp, Iso.hom_inv_id]

lemma toOver_injective : Function.Injective
    (toOverIso V : (A.restrict V.ι ≅ B.restrict V.ι) → (A.over V ≅ B.over V)) := by
  intro e f h
  have hh := congrArg (fun k => (Scheme.Modules.overEquiv V).functor.map k.hom) h
  rw [map_toOver_hom, map_toOver_hom] at hh
  apply Iso.ext
  apply (cancel_mono ((Scheme.Modules.overFunctorEquiv V).app B).inv).mp
  apply (cancel_epi ((Scheme.Modules.overFunctorEquiv V).app A).hom).mp
  simpa only [Category.assoc] using hh

variable {ι : Type u} (U : ι → X.Opens) (M : ι → X.Modules)
/-- Original scheme-local sheaf transitions, with their actual restriction
composition and inclusion-equality maps on the original triple open. -/
structure Data where
  transition : ∀ i j, (M i).restrict (U i ⊓ U j).ι ≅ (M j).restrict (U i ⊓ U j).ι
  identity : ∀ i, transition i i = Iso.refl _
  cocycle : ∀ i j k,
    schemeRestrict (transition i j) (show (U i ⊓ U j) ⊓ U k ≤ U i ⊓ U j from inf_le_left) ≪≫
      schemeRestrict (transition j k)
        (le_inf (inf_le_left.trans inf_le_right) inf_le_right) =
    schemeRestrict (transition i k)
      (le_inf (inf_le_left.trans inf_le_left) inf_le_right)

variable {U M} (D : Data U M)
/-- The original scheme triple cocycle gives the exact over-open cocycle
required by gluing. No over-open identity or scalar cocycle is an input. -/
@[expose] def overData : OpenSheafTransition318.Data U M where
  transition i j := toOverIso (U i ⊓ U j) (D.transition i j)
  identity i := by rw [D.identity]; exact toOver_refl
  cocycle i j k := by
    have h := congrArg (toOverIso ((U i ⊓ U j) ⊓ U k)) (D.cocycle i j k)
    simpa only [toOver_trans, restriction_compatible] using h
end OpenSchemeTransition318
