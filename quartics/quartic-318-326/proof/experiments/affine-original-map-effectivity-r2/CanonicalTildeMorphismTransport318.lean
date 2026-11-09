module
public import CanonicalScalarMorphismDescent318
public section
noncomputable section
namespace CanonicalTildeMorphismTransport318
open AlgebraicGeometry CategoryTheory
open AffineModuleBaseChange318 CanonicalTildeOverlap318
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable {R S : CommRingCat.{u}} (f : R ⟶ S) {M N : ModuleCat R}
  (h : (Scheme.Modules.pullback (Spec.map f)).obj (tilde M) ⟶
    (Scheme.Modules.pullback (Spec.map f)).obj (tilde N))

/-- Recover the exact scalar-extension map from the original covering
sheaf map, using the original tilde pullback comparisons at both endpoints. -/
@[expose] def moduleMap : (ModuleCat.extendScalars f.hom).obj M ⟶
    (ModuleCat.extendScalars f.hom).obj N :=
  (tilde.functor S).preimage ((TildePullback318.pullbackIso f).inv.app M ≫
    h ≫ (TildePullback318.pullbackIso f).hom.app N)

lemma moduleMap_square : (tilde.functor S).map (moduleMap f h) ≫
    (TildePullback318.pullbackIso f).inv.app N =
      (TildePullback318.pullbackIso f).inv.app M ≫ h := by
  rw [moduleMap, Functor.map_preimage]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]

/-- The original scalar/sheaf endpoint square also commutes after each
original edge pullback, using naturality of the exact tilde comparison. -/
lemma step_square {T : CommRingCat.{u}} (g : S ⟶ T) :
    (tilde.functor T).map ((ModuleCat.extendScalars g.hom).map (moduleMap f h)) ≫
      (stepIso f g N).hom =
    (stepIso f g M).hom ≫ (Scheme.Modules.pullback (Spec.map g)).map h := by
  have hn := (TildePullback318.pullbackIso g).inv.naturality (moduleMap f h)
  change (tilde.functor T).map ((ModuleCat.extendScalars g.hom).map (moduleMap f h)) ≫
      (TildePullback318.pullbackIso g).inv.app ((ModuleCat.extendScalars f.hom).obj N) =
    (TildePullback318.pullbackIso g).inv.app ((ModuleCat.extendScalars f.hom).obj M) ≫
      (Scheme.Modules.pullback (Spec.map g)).map ((tilde.functor S).map (moduleMap f h)) at hn
  simp only [stepIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv]
  rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, moduleMap_square,
    Functor.map_comp, Category.assoc]

variable (R S : CommRingCat.{u}) [Algebra R S]
  {M N : ModuleCat R}
  (h : (Scheme.Modules.pullback (Spec.map (ringMap R S))).obj (tilde M) ⟶
    (Scheme.Modules.pullback (Spec.map (ringMap R S))).obj (tilde N))

/-- Genuine canonical geometric overlap compatibility implies the original
canonical scalar-overlap square. Both named endpoint maps are preserved. -/
lemma scalar_square
    (hh : sheafOverlap R S M ≫
        (Scheme.Modules.pullback (Spec.map (rightMap R S S))).map h =
      (Scheme.Modules.pullback (Spec.map (leftMap R S S))).map h ≫ sheafOverlap R S N) :
    CanonicalScalarOverlap318.overlap R S M ≫
        (ModuleCat.extendScalars (rightMap R S S).hom).map (moduleMap (ringMap R S) h) =
      (ModuleCat.extendScalars (leftMap R S S).hom).map (moduleMap (ringMap R S) h) ≫
        CanonicalScalarOverlap318.overlap R S N := by
  apply (tilde.functor (ring R S S)).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  apply (cancel_mono (stepIso (ringMap R S) (rightMap R S S) N).hom).mp
  rw [Category.assoc, step_square, ← Category.assoc, ← canonical_square,
    Category.assoc, hh, ← Category.assoc, ← step_square, Category.assoc, canonical_square,
    ← Category.assoc]
end CanonicalTildeMorphismTransport318
