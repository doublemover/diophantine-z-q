module
public import OverlapMorphismCoaction318
public section
noncomputable section
namespace CanonicalScalarOverlap318
open AlgebraicGeometry CategoryTheory TensorProduct AffineModuleBaseChange318 AffineOverlapCoaction318
open scoped ChangeOfRings
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S]
local instance moduleR (N : ModuleCat.{u} S) : Module R N := Module.compHom N (algebraMap R S)
local instance towerR (N : ModuleCat.{u} S) : IsScalarTower R S N := IsScalarTower.of_compHom ..
abbrev base : R ⟶ ring R S S := CommRingCat.ofHom (algebraMap R (ring R S S))
lemma left_path : (leftMap R S S).hom.comp (algebraMap R S) = (base R S).hom :=
  (AffineTripleCoactionCoordinates318.base_left R S).symm
lemma right_path : (rightMap R S S).hom.comp (algebraMap R S) = (base R S).hom :=
  (AffineModuleMate318.ring_square R S S).symm.trans (left_path R S)
variable (M : ModuleCat R)
abbrev coverModule := (ModuleCat.extendScalars (algebraMap R S)).obj M
abbrev leftComparison := ScalarExtensionComposition318.comparison (algebraMap R S)
  (leftMap R S S).hom M (base R S).hom (left_path R S)
abbrev rightComparison := ScalarExtensionComposition318.comparison (algebraMap R S)
  (rightMap R S S).hom M (base R S).hom (right_path R S)

/-- The canonical scalar overlap of a genuine base module, using both
original comparisons to the same original composite scalar extension. -/
@[expose] def overlap : first R S (coverModule R S M) ⟶ second R S (coverModule R S M) :=
  (leftComparison R S M).hom ≫ (rightComparison R S M).inv

/-- The canonical overlap gives exactly the comparison coalgebra's
coaction: original scalar extension of the original adjunction unit. -/
lemma canonical_coaction : homEquiv R S (coverModule R S M) (overlap R S M) =
    (ModuleCat.extendScalars (algebraMap R S)).map
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app M) := by
  ext n
  change (homEquiv R S (coverModule R S M) (overlap R S M)).hom n =
    ((ModuleCat.extendScalars (algebraMap R S)).map
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app M)).hom n
  induction n using TensorProduct.inductionOn with
  | tmul s m =>
      rw [homEquiv_value]
      change (component R S S (coverModule R S M)).hom
        ((rightComparison R S M).inv ((leftComparison R S M).hom
          ((1 : ring R S S) ⊗ₜ[S, (leftMap R S S).hom] (s ⊗ₜ[R, algebraMap R S] m)))) = _
      rw [ScalarExtensionComposition318.comparison_tmul, one_mul,
        ScalarExtensionComposition318.comparison_inv_tmul]
      change (component R S S (coverModule R S M)).hom
        ((s ⊗ₜ[R] (1 : S)) ⊗ₜ[S, (rightMap R S S).hom]
          ((1 : S) ⊗ₜ[R, algebraMap R S] m)) = _
      rw [component_tmul, one_smul]
      rfl
  | add n m hn hm => simp only [map_add, hn, hm]

variable {N : ModuleCat S} (e : coverModule R S M ≅ N)
/-- Transport the actual canonical scalar overlap through the specified
original module comparison, retaining both scalar pullbacks of that map. -/
@[expose] def conjugated : first R S N ⟶ second R S N :=
  (ModuleCat.extendScalars (leftMap R S S).hom).map e.inv ≫ overlap R S M ≫
    (ModuleCat.extendScalars (rightMap R S S).hom).map e.hom

lemma conjugated_coaction : homEquiv R S N (conjugated R S M e) =
    e.inv ≫ (ModuleCat.extendScalars (algebraMap R S)).map
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app M) ≫
      (pullPush R S S).map e.hom := by
  have hs : overlap R S M ≫ (ModuleCat.extendScalars (rightMap R S S).hom).map e.hom =
      (ModuleCat.extendScalars (leftMap R S S).hom).map e.hom ≫ conjugated R S M e := by
    simp only [conjugated, Category.assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id, Functor.map_id, Category.id_comp]
  have h := OverlapMorphismCoaction318.module_coaction R S e.hom
    (overlap R S M) (conjugated R S M e) hs
  rw [canonical_coaction] at h
  have hh := congrArg (fun k => e.inv ≫ k) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh.symm
end CanonicalScalarOverlap318
