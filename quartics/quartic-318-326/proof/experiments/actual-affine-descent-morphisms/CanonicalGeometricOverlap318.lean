module
public import CanonicalTildeOverlap318
public section
noncomputable section
namespace CanonicalGeometricOverlap318
open AlgebraicGeometry CategoryTheory LineSheafClass318
open AffineModuleBaseChange318 OriginalLineAffineBaseChange318 CanonicalTildeOverlap318
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
variable (R S : CommRingCat.{u}) [Algebra R S] (M : ModuleCat R)
  (L : Line (Spec S))
  (e : (ModuleCat.extendScalars (algebraMap R S)).obj M ≅ OriginalLineAffineModel318.sections S L)

/-- The actual canonical overlap of the displayed pulled-back base sheaf,
transported through the original specified reconstruction comparison. -/
@[expose] def overlap : OriginalLineOverlapCoaction318.first R S L ⟶
    OriginalLineOverlapCoaction318.second R S L :=
  (Scheme.Modules.pullback (Spec.map (leftMap R S S))).map
      (coverComparison (ringMap R S) M L e).inv ≫
    sheafOverlap R S M ≫
    (Scheme.Modules.pullback (Spec.map (rightMap R S S))).map
      (coverComparison (ringMap R S) M L e).hom

/-- Both endpoint squares identify the canonical original geometric
comparison with the exact conjugated canonical scalar overlap. -/
lemma sheaf_conjugation :
    (sheafIso (leftMap R S S) L).hom ≫ overlap R S M L e ≫
      (sheafIso (rightMap R S S) L).inv =
    (tilde.functor (ring R S S)).map (CanonicalScalarOverlap318.conjugated R S M e) := by
  let A := stepIso (ringMap R S) (leftMap R S S) M
  let B := stepIso (ringMap R S) (rightMap R S S) M
  let C := (tilde.functor (ring R S S)).mapIso
    ((ModuleCat.extendScalars (leftMap R S S).hom).mapIso e)
  let D := (tilde.functor (ring R S S)).mapIso
    ((ModuleCat.extendScalars (rightMap R S S).hom).mapIso e)
  let P := (Scheme.Modules.pullback (Spec.map (leftMap R S S))).mapIso
    (coverComparison (ringMap R S) M L e)
  let Q := (Scheme.Modules.pullback (Spec.map (rightMap R S S))).mapIso
    (coverComparison (ringMap R S) M L e)
  have h := AffineSectionConjugation318.normalized (𝟭 (Spec (ring R S S)).Modules)
    A B (sheafIso (leftMap R S S) L) (sheafIso (rightMap R S S) L) P Q C D
    (endpoint (ringMap R S) (leftMap R S S) M L e)
    (endpoint (ringMap R S) (rightMap R S S) M L e) (sheafOverlap R S M)
  change _ = C.inv ≫ (A.hom ≫ sheafOverlap R S M ≫ B.inv) ≫ D.hom at h
  rw [canonical_conjugation] at h
  simpa only [overlap, CanonicalScalarOverlap318.conjugated, C, D, P, Q,
    Functor.id_map, Functor.mapIso_hom, Functor.mapIso_inv, Functor.map_comp,
    Category.assoc] using h

/-- The established original sheaf-to-module correspondence sends this
actual geometric overlap to the original conjugated scalar overlap. -/
lemma module_overlap : OriginalLineOverlapCoaction318.moduleHomEquiv R S L (overlap R S M L e) =
    CanonicalScalarOverlap318.conjugated R S M e := by
  have h := congrArg (fun k => k ≫ (sheafIso (rightMap R S S) L).hom)
    (sheaf_conjugation R S M L e)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  have hh := congrArg ((tilde.adjunction (R := ring R S S)).homEquiv _ _) h
  simp only [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    OriginalLineComparisonComposition318.sheafIso_adjoint] at hh
  apply (cancel_mono (sectionsIso (rightMap R S S) L).hom).mp
  simpa only [OriginalLineOverlapCoaction318.moduleHomEquiv_apply,
    Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh

/-- The original geometric correspondence sends the displayed canonical
sheaf overlap to exactly the transported comparison coaction. -/
lemma coaction : OriginalLineOverlapCoaction318.homEquiv R S L (overlap R S M L e) =
    e.inv ≫ (ModuleCat.extendScalars (algebraMap R S)).map
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap R S)).unit.app M) ≫
      (pullPush R S S).map e.hom := by
  change AffineOverlapCoaction318.homEquiv R S (OriginalLineAffineModel318.sections S L)
    (OriginalLineOverlapCoaction318.moduleHomEquiv R S L (overlap R S M L e)) = _
  rw [module_overlap, CanonicalScalarOverlap318.conjugated_coaction]
end CanonicalGeometricOverlap318
