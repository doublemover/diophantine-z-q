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

/-- Naturality of an adjunction mate on native functor carriers. This
categorical identity is proved before substituting the original localizations. -/
lemma adjoint_square {C E : Type*} [Category C] [Category E]
    {F : C ⥤ E} {G : E ⥤ C} (adj : F ⊣ G) {A B : C} {P Q : E}
    (e : F.obj A ⟶ P) (d : F.obj B ⟶ Q) (h : P ⟶ Q) (k : A ⟶ B)
    (he : e ≫ h=F.map k ≫ d) :
    adj.homEquiv A P e ≫ G.map h=k ≫ adj.homEquiv B Q d := by
  have hh := congrArg (adj.homEquiv A Q) he
  rw [Adjunction.homEquiv_naturality_right,Adjunction.homEquiv_naturality_left] at hh
  exact hh

/-- The established original sheaf-to-module correspondence sends this
actual geometric overlap to the original conjugated scalar overlap. -/
lemma module_overlap : OriginalLineOverlapCoaction318.moduleHomEquiv R S L (overlap R S M L e) =
    CanonicalScalarOverlap318.conjugated R S M e := by
  have h := congrArg (fun k => k ≫ (sheafIso (rightMap R S S) L).hom)
    (sheaf_conjugation R S M L e)
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h
  have hh := adjoint_square (tilde.adjunction (R:=ring R S S))
    (sheafIso (leftMap R S S) L).hom (sheafIso (rightMap R S S) L).hom
    (overlap R S M L e) (CanonicalScalarOverlap318.conjugated R S M e) h
  have hl : (tilde.adjunction (R:=ring R S S)).homEquiv
      (extendedSections (leftMap R S S) L)
      (LineSheafPullback318.line (Spec.map (leftMap R S S)) L).object
      (sheafIso (leftMap R S S) L).hom=(sectionsIso (leftMap R S S) L).hom := by
    rw [Adjunction.homEquiv_unit]
    rfl
  have hr : (tilde.adjunction (R:=ring R S S)).homEquiv
      (extendedSections (rightMap R S S) L)
      (LineSheafPullback318.line (Spec.map (rightMap R S S)) L).object
      (sheafIso (rightMap R S S) L).hom=(sectionsIso (rightMap R S S) L).hom := by
    rw [Adjunction.homEquiv_unit]
    rfl
  rw [hl,hr] at hh
  change (OriginalLineOverlapCoaction318.moduleHomEquiv R S L).toFun (overlap R S M L e)=_
  rw [OriginalLineOverlapCoaction318.moduleHomEquiv_apply]
  apply (cancel_mono (sectionsIso (rightMap R S S) L).hom).mp
  simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hh

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
